#!/usr/bin/env python3
"""Render the reviewed scientific paper with the installed native TeX engine.

Explicit read paths and a workspace-local format replace missing generated
search databases. No installation, network, or scientific-source change.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
TMP = ROOT / 'tmp_native_render'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for directory in (TMP, TMP / 'formats', TMP / 'var', TMP / 'fonts'):
        directory.mkdir(parents=True, exist_ok=True)
    source = ROOT / 'science_completion_report.tex'
    original = source.read_text()
    render_source = TMP / source.name
    render_source.write_text(original)
    env = os.environ.copy()
    env.update({
        'TEXINPUTS': '.:/usr/share/texlive/texmf-dist/tex/latex//:/usr/share/texlive/texmf-dist/tex/generic//:/usr/share/texmf/tex//',
        'TFMFONTS': '/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//',
        'VFFONTS': '/usr/share/texlive/texmf-dist/fonts/vf//:/usr/share/texmf/fonts/vf//',
        'T1FONTS': '/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//',
        'ENCFONTS': '/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//',
        'TEXFONTMAPS': str(TMP) + '//:/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//',
        'TEXFORMATS': str(TMP / 'formats') + '//',
        'TEXMFVAR': str(TMP / 'var'),
        'TEXMFCONFIG': str(TMP / 'var'),
        'VARTEXFONTS': str(TMP / 'fonts'),
        'TMPDIR': str(TMP),
        'MKTEXFMT': '0', 'MKTEXPK': '0', 'MKTEXTFM': '0',
    })
    maps = [
        Path('/usr/share/texmf/fonts/map/dvips/lm/lm.map'),
        Path('/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map'),
        Path('/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map'),
    ]
    (TMP / 'pdftex.map').write_bytes(b'\n'.join(path.read_bytes() for path in maps))

    def run(command, log_name):
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                capture_output=True, timeout=60)
        (TMP / log_name).write_text(result.stdout + '\n' + result.stderr)
        if result.returncode:
            raise RuntimeError(f'{log_name}: exit {result.returncode}\n' +
                               (result.stdout + result.stderr)[-3000:])

    pdftex = shutil.which('pdftex')
    pdflatex = shutil.which('pdflatex')
    assert pdftex and pdflatex, 'The installed TeX executables are required.'
    if not (TMP / 'formats' / 'pdflatex.fmt').is_file():
        run([pdftex, '-ini', '-etex', '-no-shell-escape', '-jobname=pdflatex',
             '-interaction=nonstopmode', '-halt-on-error',
             '-output-directory=' + str(TMP / 'formats'),
             '/usr/share/texlive/texmf-dist/tex/latex/tex-ini-files/pdflatex.ini'],
            'format_build.log')
    command = [pdflatex, '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-output-directory=' + str(TMP), str(render_source)]
    run(command, 'pass_1.stdout.log')
    run(command, 'pass_2.stdout.log')
    run(command, 'pass_3.stdout.log')
    tex_log = (TMP / 'science_completion_report.log').read_text()
    defects = re.findall(r'^.*(?:Warning|Error|Overfull|Underfull|Missing character|Undefined control sequence).*$',
                         tex_log, re.MULTILINE)
    assert not defects, defects
    output = ROOT / 'science_completion_report.pdf'
    shutil.copyfile(TMP / output.name, output)
    assert output.stat().st_size > 10000
    record = {
        'source_sha256': digest(source),
        'renderer_sha256': digest(Path(__file__)),
        'presentation_source_sha256': digest(render_source),
        'pdf_sha256': digest(output),
        'pdf_bytes': output.stat().st_size,
        'engine': 'native pdfLaTeX; three passes; shell escape disabled',
        'format_only_replacements': {},
        'mathematical_expression_replacements': 0,
        'tex_log_diagnostic_matches': defects,
        'visual_QA_pending': True,
    }
    (TMP / 'render_record.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'output': str(output), **record}, indent=2))


if __name__ == '__main__':
    main()
