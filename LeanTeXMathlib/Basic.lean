import LeanTeX
import Mathlib

/-!
# LaTeX pretty printers for mathlib

-/

open LeanTeX

namespace Mathlib.LeanTeX

open Lean
open scoped MkAppNMacro

-- Note: `HasSubset.Subset` is not in scope here
latex_pp_app_rules (const := HasSubset.Subset)
  | _, #[_, _, a, b] => do
    let a ← latexPP a
    let b ← latexPP b
    return a.protectRight 50 ++ LatexData.nonAssocOp " \\subseteq " 50 ++ b.protectLeft 50

@[latex_pp_app const.Union.union] def pp_Union := basicBinOpPrinter " \\cup " 65 .left 4
@[latex_pp_app const.Inter.inter] def pp_Inter := basicBinOpPrinter " \\cap " 70 .left 4

/-- This renders `Set.image f X` as `f[X]`, which is a reasonably common notation for set image. -/
latex_pp_app_rules (const := Set.image)
  | _, #[_, _, f, X] => do
    let f ← latexPP f
    let X ← latexPP X
    return ← f.protectRight funAppBP ++ X.brackets |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)
      |>.maybeWithTooltip s!"image of \\({X.latex.1}\\) under \\({f.latex.1}\\)"

-- Use the type itself as the universe
latex_pp_app_rules (const := Finset.univ)
  | _, #[ty, _] => latexPP ty

latex_pp_app_rules (const := Finset.prod)
| _, #[_α, _β, _inst, s, f] => do
  let set ← withExtraSmallness 2 <| latexPP s
  withBindingBodyUnusedName' f `i fun name body => do
    let pbody ← latexPP body
    let pbody := pbody.protectLeft 66
    let psum := (← (LatexData.atomString "\\prod" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ set) |>.maybeWithTooltip "Finset.prod") ++ pbody
    return psum |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

latex_pp_app_rules (const := Finset.sum)
  | _, #[_α, _β, _inst, s, f] => do
    let set ← withExtraSmallness 2 <| latexPP s
    withBindingBodyUnusedName' f `i fun name body => do
      let pbody ← latexPP body
      let pbody := pbody.protectLeft 66
      let psum := (← (LatexData.atomString "\\sum" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ set) |>.maybeWithTooltip "Finset.sum") ++ pbody
      return psum |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 65)

-- Suppress casts
latex_pp_app_rules (const := Nat.cast)
  | _, #[_, _, n] => latexPP n
latex_pp_app_rules (const := Int.cast)
  | _, #[_, _, n] => latexPP n

latex_pp_const_rule Rat := (LatexData.atomString "\\mathbb{Q}").maybeWithTooltip "Rat"

latex_pp_const_rule Real := (LatexData.atomString "\\mathbb{R}").maybeWithTooltip "Real"
latex_pp_const_rule Real.pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "real.pi"

latex_pp_app_rules (const := Real.sqrt)
  | _, #[x] => do
    let v ← latexPP x
    let (latex, bigness) := v.latex
    -- Note: using an atom, but subscripts are incompatible with the square root symbol.
    -- Assuming subscripts will never happen.
    return .Atom ("\\sqrt{" ++ latex ++ "}") bigness none none

macro "latex_pp_trig_rule" c:ident tex:str : command =>
  `(
  latex_pp_app_rules (const := $c)
    | _, #[x] => do
      let v ← latexPP x
      return LatexData.atomString $tex ++ " " ++ v.protect (funAppBP - 1)
        |>.mergeBP (lbp := .NonAssoc funAppBP) (rbp := .NonAssoc funAppBP)
  )

latex_pp_trig_rule Real.sin "\\sin"
latex_pp_trig_rule Real.cos "\\cos"
latex_pp_trig_rule Real.tan "\\tan"
latex_pp_trig_rule Real.arcsin "\\sin^{-1}"
latex_pp_trig_rule Real.arccos "\\cos^{-1}"
latex_pp_trig_rule Real.arctan "\\tan^{-1}"

latex_pp_app_rules (const := Finset.Icc)
  | _, #[_, _, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "[" ++ lo ++ ", " ++ hi ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Ico)
  | _, #[_, _, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "[" ++ lo ++ ", " ++ hi ++ ")" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Ioc)
  | _, #[_, _, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "(" ++ lo ++ ", " ++ hi ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Ioo)
  | _, #[_, _, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "(" ++ lo ++ ", " ++ hi ++ ")" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Iic)
  | _, #[_, _, _, hi] => do
    let hi ← latexPP hi
    -- using infty is not technically correct. for example, ℕ would be starting from 0
    return "(-\\infty, " ++ hi ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Iio)
  | _, #[_, _, _, hi] => do
    let hi ← latexPP hi
    return "(-\\infty, " ++ hi ++ ")" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Ici)
  | _, #[_, _, _, lo] => do
    let lo ← latexPP lo
    return "[" ++ lo ++ ", \\infty)" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Finset.Ioi)
  | _, #[_, _, _, lo] => do
    let lo ← latexPP lo
    return "(" ++ lo ++ ", \\infty)" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Set.Icc)
  | _, #[_, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "[" ++ lo ++ ", " ++ hi ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Ico)
  | _, #[_, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "[" ++ lo ++ ", " ++ hi ++ ")" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Ioc)
  | _, #[_, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "(" ++ lo ++ ", " ++ hi ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Ioo)
  | _, #[_, _, lo, hi] => do
    let lo ← latexPP lo
    let hi ← latexPP hi
    return "(" ++ lo ++ ", " ++ hi ++ ")" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Set.Iio)
  | _, #[_, _, hi] => do
    let hi ← latexPP hi
    return "(-\\infty, " ++ hi ++ ")" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Iic)
  | _, #[_, _, lo] => do
    let lo ← latexPP lo
    return "(-\\infty, " ++ lo ++ "]" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Ici)
  | _, #[_, _, lo] => do
    let lo ← latexPP lo
    return "[" ++ lo ++ ", \\infty)" |>.resetBP .Infinity .Infinity
latex_pp_app_rules (const := Set.Ioi)
  | _, #[_, _, lo] => do
    let lo ← latexPP lo
    return "(" ++ lo ++ ", \\infty)" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Finset.range)
  | _, #[hi] => do
    let hi ← latexPP hi
    return "[0, " ++ hi ++ ")" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Nat.ceil)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\left\\lceil " ++ e ++ "\\right\\rceil" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Nat.floor)
  | _, #[_, _, _, e] => do
    let e ← LeanTeX.latexPP e
    return "\\left\\lfloor " ++ e ++ "\\right\\rfloor" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Max.max)
  | _, #[_, _, a, b] => do
    let a ← LeanTeX.latexPP a
    let b ← LeanTeX.latexPP b
    return "\\max(" ++ a ++ "," ++ b ++ ")" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Min.min)
  | _, #[_, _, a, b] => do
    let a ← LeanTeX.latexPP a
    let b ← LeanTeX.latexPP b
    return "\\min(" ++ a ++ "," ++ b ++ ")" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := Singleton.singleton)
  | _, #[_, _, _, a] => do
    let a ← LeanTeX.latexPP a
    return "\\{ " ++ a ++ " \\}" |>.resetBP .Infinity .Infinity

latex_pp_app_rules (const := DirectSum)
  | _, #[ι, β, _inst] => do
    let pι ← withExtraSmallness 2 <| latexPP ι
    withBindingBodyUnusedName' β `i fun name body => do
      let pbody ← latexPP body
      let psum := (← (LatexData.atomString "\\bigoplus" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ pι) |>.maybeWithTooltip "DirectSum") ++ pbody
      return psum |>.resetBP (rbp := .NonAssoc 0)

latex_pp_app_rules (const := TensorProduct)
  | _, #[R, _, M, N, _, _, _, _] => do
    let pR ← latexPP R
    let pM ← latexPP M
    let pN ← latexPP N
    return pM.protectRight 100 ++ (LatexData.atomString "\\otimes" |>.sub pR) ++ pN.protectLeft 100

latex_pp_app_rules (const := PiTensorProduct)
  | _, #[ι, R, _, s, _, _] => do
    let pι ← latexPP ι
    let _pR ← latexPP R
    withBindingBodyUnusedName' s `i fun name body => do
      let pbody ← latexPP body
      let psum := (← (LatexData.atomString "\\bigotimes" |>.bigger 1).sub (s!"{name.toLatex} \\in " ++ pι) |>.maybeWithTooltip "PiTensorProduct") ++ pbody
      return psum |>.resetBP (rbp := .NonAssoc 0)
