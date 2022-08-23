import data.real.basic
import data.finset.basic
import data.analysis.filter
import topology.basic
import analysis.calculus.mean_value
import tactic

/-
Как установить:
https://leanprover-community.github.io/install/windows.html
После установки elan и пакета mathlibtools для python через pip, выполнить
leanproject get-mathlib-cache, чтобы скачать уже собранный mathlib.

Источники:
https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/

https://leanprover-community.github.io/100.html
https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html#the-existential-quantifier
https://leanprover.github.io/theorem_proving_in_lean/tactics.html
https://leanprover-community.github.io/mathlib_docs/order/filter/basic.html
https://leanprover.github.io/logic_and_proof/first_order_logic_in_lean.html
-/

-- constants a b : ℝ


open filter set
open_locale filter topological_space pointwise

/-
notation a `<` b := real.lt_cauchy a b
notation a `=` b := real.equiv_Cauchy a b
notation a `≤` b := (a < b) ∨ (a = b)
-/

/-

notation `[` a `;` b `]` := set.Icc a b

constant f: [a; b] → ℝ

definition segment_partitions := { P | P ⊆ [a; b] ∧ set.finite P ∧ a ∈ P ∧ b ∈ P }

constant P: segment_partitions

#check P ∈ segment_partitions-/


/- #check set.finite.to_finset P-/

/- #check finset.to_list (set.to_finset P) -/

/- definition darboux_lower_sum := (finset.sort set.to_finite P) -/

definition series_partial_sum (series_items: ℕ → ℝ): ℕ → ℝ :=
  (λ (n : ℕ), (finset.range n).sum (λ (k : ℕ), series_items k))
/-structure series (item_func: ℕ → ℝ): Type :=
  (item : ℕ → ℝ := item_func)
  (partial_sum: ℕ → ℝ := series_partial_sum item_func) -/

notation `|` x `|` := algebra.abs x

definition sequence_converges (seq_a: ℕ → ℝ): Prop := ∃ (l : ℝ), ∀ (ε : ℝ), (ε > 0 → (∃(N : ℕ), ∀ (n : ℕ), n > N → | seq_a n - l | < ε))

definition series_converges (series_a: ℕ → ℝ) /-(series_a: series series_item_a)-/ : Prop := sequence_converges (series_partial_sum series_a)

constant series_a: ℕ → ℝ
--#check ∀ ε > 0, ∃ N ∈ ℕ, ∀ n > N, ∀ (p : ℕ), ((finset.range p).sum (λ (k : ℕ), series_a (n + k))) < ε

definition cauchy_sequence_condition (seq_a: ℕ → ℝ) := ∀ (ε : ℝ), (ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n > N → (∀ (p : ℕ),
    (seq_a (n + p) - seq_a n) < ε)))

theorem cauchy_for_sequences (seq_a: ℕ → ℝ):
  (sequence_converges seq_a) ↔ (cauchy_sequence_condition seq_a)
:=
begin
  apply iff.intro,

  assume h : sequence_converges seq_a,
  intro ε,
  assume h₂ : (ε > 0),
  exists.intro l from h,


end


theorem cauchy_for_series (series_a: ℕ → ℝ):
  (series_converges series_a) ↔
  ∀ (ε : ℝ), (ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n > N → (∀ (p : ℕ),
    (finset.range p).sum (λ (k : ℕ), series_a (n + k)) < ε
  )))
:=
begin
  sorry,
end
/- theorem (a_n: series) (b_n: series) : () := sorry,-/
