import PhotonMomentPolynomial
import Mathlib.Tactic.FinCases
open PhotonGeometry
namespace PhotonConcreteVectors
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
noncomputable def A0 : Fin 0 → ℂ := Fin.elim0
noncomputable def A1 : Fin 1 → ℂ := Fin.snoc A0 thetaPlus
noncomputable def A2 : Fin 2 → ℂ := Fin.snoc A1 thetaPlus
noncomputable def A3 : Fin 3 → ℂ := Fin.snoc A2 thetaPlus
noncomputable def A4 : Fin 4 → ℂ := Fin.snoc A3 thetaPlus
noncomputable def A5 : Fin 5 → ℂ := Fin.snoc A4 thetaPlus
noncomputable def A6 : Fin 6 → ℂ := Fin.snoc A5 thetaMinus
noncomputable def A7 : Fin 7 → ℂ := Fin.snoc A6 thetaMinus
noncomputable def A8 : Fin 8 → ℂ := Fin.snoc A7 thetaMinus
noncomputable def A9 : Fin 9 → ℂ := Fin.snoc A8 thetaMinus
noncomputable def A10 : Fin 10 → ℂ := Fin.snoc A9 thetaMinus
noncomputable def A11 : Fin 11 → ℂ := Fin.snoc A10 phiPlus
noncomputable def A12 : Fin 12 → ℂ := Fin.snoc A11 phiPlus
noncomputable def A13 : Fin 13 → ℂ := Fin.snoc A12 phiPlus
noncomputable def A14 : Fin 14 → ℂ := Fin.snoc A13 phiPlus
noncomputable def A15 : Fin 15 → ℂ := Fin.snoc A14 phiMinus
noncomputable def A16 : Fin 16 → ℂ := Fin.snoc A15 phiMinus
noncomputable def A17 : Fin 17 → ℂ := Fin.snoc A16 phiMinus
noncomputable def A18 : Fin 18 → ℂ := Fin.snoc A17 phiMinus
noncomputable def A19 : Fin 19 → ℂ := Fin.snoc A18 1
noncomputable def A20 : Fin 20 → ℂ := Fin.snoc A19 1
noncomputable def A21 : Fin 21 → ℂ := Fin.snoc A20 (-1)
noncomputable def A22 : Fin 22 → ℂ := Fin.snoc A21 (r ^ 1 * thetaPlus)
noncomputable def A23 : Fin 23 → ℂ := Fin.snoc A22 (r ^ 1 * thetaPlus)
noncomputable def A24 : Fin 24 → ℂ := Fin.snoc A23 (r ^ 1 * thetaPlus)
noncomputable def A25 : Fin 25 → ℂ := Fin.snoc A24 (r ^ 1 * thetaPlus)
noncomputable def A26 : Fin 26 → ℂ := Fin.snoc A25 (r ^ 1 * thetaPlus)
noncomputable def A27 : Fin 27 → ℂ := Fin.snoc A26 (r ^ 1 * thetaMinus)
noncomputable def A28 : Fin 28 → ℂ := Fin.snoc A27 (r ^ 1 * thetaMinus)
noncomputable def A29 : Fin 29 → ℂ := Fin.snoc A28 (r ^ 1 * thetaMinus)
noncomputable def A30 : Fin 30 → ℂ := Fin.snoc A29 (r ^ 1 * thetaMinus)
noncomputable def A31 : Fin 31 → ℂ := Fin.snoc A30 (r ^ 1 * thetaMinus)
noncomputable def A32 : Fin 32 → ℂ := Fin.snoc A31 (r ^ 1 * phiPlus)
noncomputable def A33 : Fin 33 → ℂ := Fin.snoc A32 (r ^ 1 * phiPlus)
noncomputable def A34 : Fin 34 → ℂ := Fin.snoc A33 (r ^ 1 * phiPlus)
noncomputable def A35 : Fin 35 → ℂ := Fin.snoc A34 (r ^ 1 * phiPlus)
noncomputable def A36 : Fin 36 → ℂ := Fin.snoc A35 (r ^ 1 * phiMinus)
noncomputable def A37 : Fin 37 → ℂ := Fin.snoc A36 (r ^ 1 * phiMinus)
noncomputable def A38 : Fin 38 → ℂ := Fin.snoc A37 (r ^ 1 * phiMinus)
noncomputable def A39 : Fin 39 → ℂ := Fin.snoc A38 (r ^ 1 * phiMinus)
noncomputable def A40 : Fin 40 → ℂ := Fin.snoc A39 (r ^ 1 * 1)
noncomputable def A41 : Fin 41 → ℂ := Fin.snoc A40 (r ^ 1 * 1)
noncomputable def A42 : Fin 42 → ℂ := Fin.snoc A41 (r ^ 1 * (-1))
noncomputable def A43 : Fin 43 → ℂ := Fin.snoc A42 (r ^ 3 * thetaPlus)
noncomputable def A44 : Fin 44 → ℂ := Fin.snoc A43 (r ^ 3 * thetaPlus)
noncomputable def A45 : Fin 45 → ℂ := Fin.snoc A44 (r ^ 3 * thetaPlus)
noncomputable def A46 : Fin 46 → ℂ := Fin.snoc A45 (r ^ 3 * thetaPlus)
noncomputable def A47 : Fin 47 → ℂ := Fin.snoc A46 (r ^ 3 * thetaPlus)
noncomputable def A48 : Fin 48 → ℂ := Fin.snoc A47 (r ^ 3 * thetaMinus)
noncomputable def A49 : Fin 49 → ℂ := Fin.snoc A48 (r ^ 3 * thetaMinus)
noncomputable def A50 : Fin 50 → ℂ := Fin.snoc A49 (r ^ 3 * thetaMinus)
noncomputable def A51 : Fin 51 → ℂ := Fin.snoc A50 (r ^ 3 * thetaMinus)
noncomputable def A52 : Fin 52 → ℂ := Fin.snoc A51 (r ^ 3 * thetaMinus)
noncomputable def A53 : Fin 53 → ℂ := Fin.snoc A52 (r ^ 3 * phiPlus)
noncomputable def A54 : Fin 54 → ℂ := Fin.snoc A53 (r ^ 3 * phiPlus)
noncomputable def A55 : Fin 55 → ℂ := Fin.snoc A54 (r ^ 3 * phiPlus)
noncomputable def A56 : Fin 56 → ℂ := Fin.snoc A55 (r ^ 3 * phiPlus)
noncomputable def A57 : Fin 57 → ℂ := Fin.snoc A56 (r ^ 3 * phiMinus)
noncomputable def A58 : Fin 58 → ℂ := Fin.snoc A57 (r ^ 3 * phiMinus)
noncomputable def A59 : Fin 59 → ℂ := Fin.snoc A58 (r ^ 3 * phiMinus)
noncomputable def A60 : Fin 60 → ℂ := Fin.snoc A59 (r ^ 3 * phiMinus)
noncomputable def A61 : Fin 61 → ℂ := Fin.snoc A60 (r ^ 3 * 1)
noncomputable def A62 : Fin 62 → ℂ := Fin.snoc A61 (r ^ 3 * 1)
noncomputable def A63 : Fin 63 → ℂ := Fin.snoc A62 (r ^ 3 * (-1))
theorem A_binding : A63 = geometryA.get := by
  funext i
  fin_cases i
  · change _ = (thetaPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (1 : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = (1 : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((-1) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * 1) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * 1) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r * (-1)) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * 1) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * 1) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
  · change _ = ((r ^ 3 * (-1)) : ℂ)
    norm_num [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46, A47, A48, A49, A50, A51, A52, A53, A54, A55, A56, A57, A58, A59, A60, A61, A62, A63, Fin.snoc]
#print axioms A_binding
noncomputable def B0 : Fin 0 → ℂ := Fin.elim0
noncomputable def B1 : Fin 1 → ℂ := Fin.snoc B0 thetaPlus
noncomputable def B2 : Fin 2 → ℂ := Fin.snoc B1 thetaPlus
noncomputable def B3 : Fin 3 → ℂ := Fin.snoc B2 thetaPlus
noncomputable def B4 : Fin 4 → ℂ := Fin.snoc B3 thetaPlus
noncomputable def B5 : Fin 5 → ℂ := Fin.snoc B4 thetaPlus
noncomputable def B6 : Fin 6 → ℂ := Fin.snoc B5 thetaMinus
noncomputable def B7 : Fin 7 → ℂ := Fin.snoc B6 thetaMinus
noncomputable def B8 : Fin 8 → ℂ := Fin.snoc B7 thetaMinus
noncomputable def B9 : Fin 9 → ℂ := Fin.snoc B8 thetaMinus
noncomputable def B10 : Fin 10 → ℂ := Fin.snoc B9 thetaMinus
noncomputable def B11 : Fin 11 → ℂ := Fin.snoc B10 phiPlus
noncomputable def B12 : Fin 12 → ℂ := Fin.snoc B11 phiPlus
noncomputable def B13 : Fin 13 → ℂ := Fin.snoc B12 phiPlus
noncomputable def B14 : Fin 14 → ℂ := Fin.snoc B13 phiPlus
noncomputable def B15 : Fin 15 → ℂ := Fin.snoc B14 phiMinus
noncomputable def B16 : Fin 16 → ℂ := Fin.snoc B15 phiMinus
noncomputable def B17 : Fin 17 → ℂ := Fin.snoc B16 phiMinus
noncomputable def B18 : Fin 18 → ℂ := Fin.snoc B17 phiMinus
noncomputable def B19 : Fin 19 → ℂ := Fin.snoc B18 1
noncomputable def B20 : Fin 20 → ℂ := Fin.snoc B19 1
noncomputable def B21 : Fin 21 → ℂ := Fin.snoc B20 (-1)
noncomputable def B22 : Fin 22 → ℂ := Fin.snoc B21 (r ^ 2 * thetaPlus)
noncomputable def B23 : Fin 23 → ℂ := Fin.snoc B22 (r ^ 2 * thetaPlus)
noncomputable def B24 : Fin 24 → ℂ := Fin.snoc B23 (r ^ 2 * thetaPlus)
noncomputable def B25 : Fin 25 → ℂ := Fin.snoc B24 (r ^ 2 * thetaPlus)
noncomputable def B26 : Fin 26 → ℂ := Fin.snoc B25 (r ^ 2 * thetaPlus)
noncomputable def B27 : Fin 27 → ℂ := Fin.snoc B26 (r ^ 2 * thetaMinus)
noncomputable def B28 : Fin 28 → ℂ := Fin.snoc B27 (r ^ 2 * thetaMinus)
noncomputable def B29 : Fin 29 → ℂ := Fin.snoc B28 (r ^ 2 * thetaMinus)
noncomputable def B30 : Fin 30 → ℂ := Fin.snoc B29 (r ^ 2 * thetaMinus)
noncomputable def B31 : Fin 31 → ℂ := Fin.snoc B30 (r ^ 2 * thetaMinus)
noncomputable def B32 : Fin 32 → ℂ := Fin.snoc B31 (r ^ 2 * phiPlus)
noncomputable def B33 : Fin 33 → ℂ := Fin.snoc B32 (r ^ 2 * phiPlus)
noncomputable def B34 : Fin 34 → ℂ := Fin.snoc B33 (r ^ 2 * phiPlus)
noncomputable def B35 : Fin 35 → ℂ := Fin.snoc B34 (r ^ 2 * phiPlus)
noncomputable def B36 : Fin 36 → ℂ := Fin.snoc B35 (r ^ 2 * phiMinus)
noncomputable def B37 : Fin 37 → ℂ := Fin.snoc B36 (r ^ 2 * phiMinus)
noncomputable def B38 : Fin 38 → ℂ := Fin.snoc B37 (r ^ 2 * phiMinus)
noncomputable def B39 : Fin 39 → ℂ := Fin.snoc B38 (r ^ 2 * phiMinus)
noncomputable def B40 : Fin 40 → ℂ := Fin.snoc B39 (r ^ 2 * 1)
noncomputable def B41 : Fin 41 → ℂ := Fin.snoc B40 (r ^ 2 * 1)
noncomputable def B42 : Fin 42 → ℂ := Fin.snoc B41 (r ^ 2 * (-1))
noncomputable def B43 : Fin 43 → ℂ := Fin.snoc B42 (r ^ 3 * thetaPlus)
noncomputable def B44 : Fin 44 → ℂ := Fin.snoc B43 (r ^ 3 * thetaPlus)
noncomputable def B45 : Fin 45 → ℂ := Fin.snoc B44 (r ^ 3 * thetaPlus)
noncomputable def B46 : Fin 46 → ℂ := Fin.snoc B45 (r ^ 3 * thetaPlus)
noncomputable def B47 : Fin 47 → ℂ := Fin.snoc B46 (r ^ 3 * thetaPlus)
noncomputable def B48 : Fin 48 → ℂ := Fin.snoc B47 (r ^ 3 * thetaMinus)
noncomputable def B49 : Fin 49 → ℂ := Fin.snoc B48 (r ^ 3 * thetaMinus)
noncomputable def B50 : Fin 50 → ℂ := Fin.snoc B49 (r ^ 3 * thetaMinus)
noncomputable def B51 : Fin 51 → ℂ := Fin.snoc B50 (r ^ 3 * thetaMinus)
noncomputable def B52 : Fin 52 → ℂ := Fin.snoc B51 (r ^ 3 * thetaMinus)
noncomputable def B53 : Fin 53 → ℂ := Fin.snoc B52 (r ^ 3 * phiPlus)
noncomputable def B54 : Fin 54 → ℂ := Fin.snoc B53 (r ^ 3 * phiPlus)
noncomputable def B55 : Fin 55 → ℂ := Fin.snoc B54 (r ^ 3 * phiPlus)
noncomputable def B56 : Fin 56 → ℂ := Fin.snoc B55 (r ^ 3 * phiPlus)
noncomputable def B57 : Fin 57 → ℂ := Fin.snoc B56 (r ^ 3 * phiMinus)
noncomputable def B58 : Fin 58 → ℂ := Fin.snoc B57 (r ^ 3 * phiMinus)
noncomputable def B59 : Fin 59 → ℂ := Fin.snoc B58 (r ^ 3 * phiMinus)
noncomputable def B60 : Fin 60 → ℂ := Fin.snoc B59 (r ^ 3 * phiMinus)
noncomputable def B61 : Fin 61 → ℂ := Fin.snoc B60 (r ^ 3 * 1)
noncomputable def B62 : Fin 62 → ℂ := Fin.snoc B61 (r ^ 3 * 1)
noncomputable def B63 : Fin 63 → ℂ := Fin.snoc B62 (r ^ 3 * (-1))
theorem B_binding : B63 = geometryB.get := by
  funext i
  fin_cases i
  · change _ = (thetaPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (thetaMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiPlus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (phiMinus : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (1 : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = (1 : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((-1) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * 1) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * 1) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 2 * (-1)) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * thetaMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiPlus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * phiMinus) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * 1) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * 1) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
  · change _ = ((r ^ 3 * (-1)) : ℂ)
    norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35, B36, B37, B38, B39, B40, B41, B42, B43, B44, B45, B46, B47, B48, B49, B50, B51, B52, B53, B54, B55, B56, B57, B58, B59, B60, B61, B62, B63, Fin.snoc]
#print axioms B_binding
end PhotonConcreteVectors
