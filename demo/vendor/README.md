# Offline Three.js dependency

`three-orbit.min.js` bundles the selected Three.js 0.186.1 exports and its
`OrbitControls` into one classic script. It exposes `window.PhotonThree` for
`../scene.js`. All renderer code is served locally; the illustration does not
fetch libraries, textures, models, fonts, or other resources at runtime.

Three.js and OrbitControls are distributed under the original
[MIT license](LICENSE-three.txt), copied without changes from the official npm
archive. Project code in `../scene.js` is separate from the vendored bundle.
The manifest records the original package's SHA-512 integrity value and SHA-256,
the precise build options, and SHA-256 hashes of the bundle, entry source, and
license. No package installation scripts were executed.

Verify the distributed bytes from the repository root:

```sh
python demo/vendor/build_vendor.py --verify-only
```

Rebuild on x86-64 Windows or Linux with Python 3.11 or later:

```sh
python demo/vendor/build_vendor.py --work-dir build/three-rebuild
```

The output directory must be new. The helper downloads only the manifest's
official npm Three.js archive and the matching esbuild 0.25.12 platform archive,
checks both SHA-512 and SHA-256 before extraction, verifies the extracted esbuild
executable, and runs that executable without npm or installation scripts. It
compares the resulting bundle byte for byte through its SHA-256 and leaves the
distributed files unchanged. The build-only esbuild executable is MIT-licensed;
its binary and package are not included in this repository.

For an offline rebuild, first place the exact archives named in the manifest
in a local directory, then add `--archive-dir PATH_TO_ARCHIVES`. Runtime use of
the demonstration requires neither Python nor these build archives.
