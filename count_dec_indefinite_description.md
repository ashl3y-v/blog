I recently had an idea to produce a function similar to `Classical.choose` for any countable set

Here are some utilities based on the axiom of choice

```lean
axiom Classical.choice {α : Sort u} : Nonempty α → α

noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
```

`Classical.choose` is used much much more frequently than `Classical.choice` so I decided to make a version of indefinite description

Lean provides `Nat.findX` (`Nat.find` and `Nat.find_spec` get the components of the subtype) which is essentially linear search, I noticed this is almost indefinite description for `Nat` with only the additional requirement of decidability of the predicate `p` and is computable

```lean
variable [DecidablePred p] (H : ∃ n, p n)

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun n h => absurd h (Nat.not_lt_zero _)
```

In the case of classical reasoning this becomes noncomputable but the type signature coincides with actual indefinite description for `Nat` because all propositions are (non-constructively) proven to be decidable
Thus, this method, for `Nat` at least, has no downsides, and this will be generalized to all countable types

The first theorem contains all the classical reasoning to transform a proof of existence of an element `x` for which the predicate holds to a proof of existence of an element `n` of `Nat`, for which the predicate holds on the image under the surjection from `Nat`

The second uses `Nat.findX` to iterate over all elements of `Nat` and check the predicate on their image, it is guaranteed that this will terminate because of the proof obtained from `exists_nat_mapped_to`

```lean
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Nat.Find

open Function

theorem exists_nat_mapped_to {p : α → Prop} (h : ∃ x, p x) (f : {g : ℕ → α // Surjective g}) :
    ∃ n, p (f.1 n) :=
  let ⟨x, hx⟩ := h
  let ⟨n, hn⟩ := f.2 x
  ⟨n, hn ▸ hx⟩

def countable_indefinite_description {α : Sort u} {p : α → Prop} [DecidablePred p]
    (f : {g : ℕ → α // Surjective g}) (h : ∃ x, p x) : {x : α // p x} :=
  let ⟨m, hm⟩ := Nat.findX (exists_nat_mapped_to h f)
  ⟨f.1 m, hm.1⟩
```

This has no downside in comparison to ordinary `Classical.choose` on a countable type, because under classical assumptions all predicates are deciable and all the functions may use classical methods

The upside is that these require no new axioms which using choice would, and can actually be computed, although this may take an arbitrarily large finite amount of time and resources, but the alternative is impossibility of computation so it's still an advantage

Since constructive mathematics is so poorly supported in Lean the definitions here are not the best they could be but that's mostly notational and in terms of precision (impossible to require a function be computable to my knowledge)

In terms of ease of use it's significantly lacking relative to `Classical.choose` which requires neither a proof of countability or decidability of the predicate which are often inconvenient to prove even if they are true, and Lean's `Countable` predicate uses an injection which would be less convenient due to its surjective inverse being noncomputable without more conditions
