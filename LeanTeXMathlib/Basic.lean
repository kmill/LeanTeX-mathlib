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

latex_pp_const_rule Rat := (LatexData.atomString "\\mathbb{Q}").maybeWithTooltip "Rat"

latex_pp_const_rule Real := (LatexData.atomString "\\mathbb{R}").maybeWithTooltip "Real"
latex_pp_const_rule Real.pi := LatexData.atomString "\\pi" |>.maybeWithTooltip "real.pi"
