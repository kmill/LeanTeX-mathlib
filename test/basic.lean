import LeanTeXMathlib
import Lean.Elab.Tactic.Guard

set_option linter.unusedVariables false

open Lean

def a : Nat := 22

def f : Nat → Nat → Nat := λ x y => x + y

def g : Unit → Nat := λ _ => 22

section
variable (b : Nat) (s : Finset Nat) (t : Nat → Finset Nat) (c : Nat → Real → Real) (x : Real)

/-- info: \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex s.sum (λ x => x + 1)
/-- info: \sum_{x \in s}2 \cdot x -/
#guard_msgs in #latex s.sum (λ x => 2 * x)
/-- info: \left(\sum_{x \in s}(x + 1)\right) \cdot \text{a} -/
#guard_msgs in #latex s.sum (λ x => x + 1) * a
/-- info: \text{a} \cdot \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex a * s.sum (λ x => x + 1)
/-- info: \left(\sum_{x \in s}(x + 1)\right) + \text{a} -/
#guard_msgs in #latex s.sum (λ x => x + 1) + a
/-- info: \text{a} + \sum_{x \in s}(x + 1) -/
#guard_msgs in #latex a + s.sum (λ x => x + 1)
/-- info: \left(\sum_{x \in s}(x + 1)\right) \cdot \sum_{x \in s}2 \cdot x -/
#guard_msgs in #latex s.sum (λ x => x + 1) * s.sum (λ x => 2 * x)
/-- info: (c : \mathbb{N}) \mapsto c \cdot \sum_{x \in s}\sum_{y \in t_{x}}x \cdot y -/
#guard_msgs in #latex λ (c : Nat) => c * s.sum (λ x => (t x).sum (λ y => x * y))
/-- info: \sum_{i \in s}\text{id}(i) -/
#guard_msgs in #latex s.sum id

open LeanTeX in
/-- An experiment: use a subscript for an argument. Represents `Fin n` as `\mathbb{N}_{<n}` -/
-- TODO make work for multi-argument like Nat → Nat → Real → Real
latex_pp_app_rules (kind := any) (paramKinds := params)
  | f, #[n] => do
    if params[0]!.bInfo.isExplicit && params[0]!.type.isConstOf `Nat then
      let f ← latexPP f
      let n ← withExtraSmallness 2 <| latexPP n
      return f.sub n
    else
      failure

/-- info: (f : \mathbb{N} \to \mathbb{N}) \mapsto \left(\sum_{i \in s}f_{i}\right)^{2} -/
#guard_msgs in #latex λ (f : Nat → Nat) => (s.sum f)^2

#texify s.sum (λ x => x + 1)
#texify s.sum (λ x => 2 * x)
#texify s.sum (λ x => x + 1) * a
#texify a * s.sum (λ x => x + 1)
#texify s.sum (λ x => x + 1) + a
#texify a + s.sum (λ x => x + 1)
#texify s.sum (λ x => x + 1) * s.sum (λ x => 2 * x)
#texify λ (c : Nat) => c * s.sum (λ x => (t x).sum (λ y => x * y))
#texify s.sum id

#texify Real.arcsin (Real.cos 2)


/-- info: (0, \frac{\pi}{2}) -/
#guard_msgs in #latex Set.Ioo 0 (Real.pi / 2)

/-- info: [0, \frac{\pi}{2}) -/
#guard_msgs in #latex Set.Ico 0 (Real.pi / 2)

/-- info: (0, \frac{\pi}{2}] -/
#guard_msgs in #latex Set.Ioc 0 (Real.pi / 2)

/-- info: [0, \frac{\pi}{2}] -/
#guard_msgs in #latex Set.Icc 0 (Real.pi / 2)

/-- info: (-\infty, 5) -/
#guard_msgs in #latex Set.Iio 5

/-- info: (-\infty, 5] -/
#guard_msgs in #latex Set.Iic 5

/-- info: [5, \infty) -/
#guard_msgs in #latex Set.Ici 5

/-- info: (5, \infty) -/
#guard_msgs in #latex Set.Ioi 5

/-- info: 3^{-1} -/
#guard_msgs in #latex (3:ℝ)⁻¹

open scoped DirectSum

#texify ⨁ i, (Fin i → ℝ)
#texify (⨁ i, Fin (i + 1)) → ℝ

end

-- https://github.com/ldct/LeanGT/blob/main/LeanGT/TexifyDemo.lean

example (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a*b*c = 1) :
    3 ≤ Real.sqrt ((a + b) / (a + 1)) + Real.sqrt ((b + c) / (b + 1)) + Real.sqrt ((c + a) / (c + 1)) := by
  texify
  sorry

example (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
  texify
  sorry

theorem imo1966_p4 (n : ℕ) (x : ℝ)
    (hx : ∀ t : ℕ, ∀ k : ℤ, x ≠ k * Real.pi / 2^t) :
    ∑ i ∈ Finset.range n, 1 / Real.sin (2^(i + 1) * x) =
    1 / Real.tan x - 1 / Real.tan (2^n * x) := by
  texify
  sorry
