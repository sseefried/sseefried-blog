% Compositional Correctness
% Sean Seefried
% Tue 22 Feb 2022

## Introduction

Proving programs correct is generally considered to be much harder than simply writing programs. There is quite a bit of evidence to support this position even though I will not go into it today. Conal Elliott has a hunch about why this is. He thinks that main reason that proof is so difficultis that, most of the time, people attempt to prove properties about existing systems; systems that were designed in the absence of mathematical constraints.

If "proving only at the end" is the main reason for the difficulty of proof, then it may be the case that _simultaneously_ proving and writing our programs is the solution.

It is well-recognised that composing programs from simpler building blocks is a good way to construct larger programs. Another well-recognised "good thing" is the principle of _compositionality_ which says that when trying to reason about the composition of A and B, it is desirable that one should just be able to reason about A and B separately. [TODO: Find better formulations of the principle of compositionality].

What if one could compose programs _and_ their proofs simulatenously? This is eminently doable in Agda. Conal has coined a name for this technique: _compositional correctness_.

In this post we will look at an example of this in action.

## Proving at the end

Define `splitPermute`

[TODO: Reference previous blog post]

```agda
  splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m + n) → 𝔽 (n + m))
  splitPermute m {n} = join n m ∘ swap ∘ splitAt m
```

Prove later:

```agda
  inverse : {m n : ℕ} → splitPermute n ∘ splitPermute m ≗ id
  inverse {m} {n} =
    begin
      (splitPermute n ∘ splitPermute m)                             ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n) ∘ (join n m ∘ swap ∘ splitAt m) ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m)   ≈⟨ cong-[ join m n ∘ swap ]∘⟨ splitAt-join n m ⟩∘[ swap ∘ splitAt m ] ⟩
      (join m n ∘ swap ∘ swap ∘ splitAt m)                          ≈⟨ cong-[ join m n ]∘⟨ swap-involutive ⟩∘[ splitAt m ] ⟩
      (join m n ∘ splitAt m)                                        ≈⟨ join-splitAt m n ⟩
      id
    ∎
    where
      open import Relation.Binary.PropositionalEquality
      open import Relation.Binary.Reasoning.Setoid (𝔽 (m + n) →-setoid 𝔽 (m + n))
```

Construct bijection:

```agda
  splitPermute↔ : (m : ℕ) {n : ℕ} → (𝔽 (m + n) ↔ 𝔽 (n + m))
  splitPermute↔ m {n} = mk↔′ (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n}
```
## Via _compositional correctness_

But there is a better way! The beautiful thing about bijections -- called `Inverse`s in Agda -- is that they have proofs bundled together with the programs. This is just what we need for _compositional correctness_.

I'll jump straight to the solution.

```agda
  splitPermute↔ : (m : ℕ) {n : ℕ} → 𝔽 (m + n) ↔ 𝔽 (n + m)
  splitPermute↔ m {n} = +↔⊎ {m} {n} ∘-↔ (swap↔ ∘-↔ flip +↔⊎)
```

That's it. The function, its inverse and accompanying proofs of invertibility/congruence have all been defined _in a single line_.

In order to understand this code you will need to know about `+↔⊎` and `swap↔`. `+↔⊎` is defined in module `Data.Sum.Properties` and has the following definition:

```agda
+↔⊎ : ∀ {m n} → Fin (m ℕ.+ n) ↔ (Fin m ⊎ Fin n)
+↔⊎ {m} {n} = mk↔′ (splitAt m {n}) (join m n) (splitAt-join m n) (join-splitAt m n)
```

Function `swap↔` is something that I had to write myself even though all the building blocks were already present in `Data.Sum` and `Data.Sum.Properties`.

```agda
swap↔ : ∀ {a b} {A : Set a} {B : Set b} → (A ⊎ B) ↔ (B ⊎ A)
swap↔ {a} {b} {A} {B} = mk↔′ swap swap swap-involutive swap-involutive
```

There was also another piece of the puzzle missing which was a `flip` function that takes
a bijection and simulteneously "flips" `f` and `f⁻¹` and the proofs of invertibility/congruence.


```agda
flip : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → B ↔ A
flip A↔B =
    record { f = f⁻¹ A↔B
           ; f⁻¹ = f A↔B
           ; cong₁ = cong₂ A↔B
           ; cong₂ = cong₁ A↔B
           ; inverse = ×-swap (inverse A↔B) }
    where
      open import Data.Product using () renaming (swap to ×-swap)
```

### Why does this work?

The magic lies in the `∘-↔` operator defined in module `Function.Construct.Composition`. It's a synonym for `inverse` which is defined as:

```agda
inverse : Inverse R S → Inverse S T → Inverse R T
inverse inv₁ inv₂ = record
    { f       = G.f ∘ F.f
    ; f⁻¹     = F.f⁻¹ ∘ G.f⁻¹
    ; cong₁   = congruent (≈ R) (≈ S) (≈ T) F.cong₁ G.cong₁
    ; cong₂   = congruent (≈ T) (≈ S) (≈ R) G.cong₂ F.cong₂
    ; inverse = inverseᵇ (≈ R) (≈ S) (≈ T) _ G.f⁻¹ (trans R) (trans T) G.cong₁ F.cong₂ F.inverse G.inverse
    } where module F = Inverse inv₁; module G = Inverse inv₂
```

One can further understand this code by looking at:

```agda
  inverseˡ : Transitive ≈₃ → Congruent ≈₂ ≈₃ g →
             Inverseˡ ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₂ ≈₃ g g⁻¹ →
             Inverseˡ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseˡ trn g-cong f-inv g-inv x = trn (g-cong (f-inv _)) (g-inv x)

  inverseʳ : Transitive ≈₁ → Congruent ≈₂ ≈₁ f⁻¹ →
             Inverseʳ ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₂ ≈₃ g g⁻¹ →
             Inverseʳ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseʳ trn f⁻¹-cong f-inv g-inv x = trn (f⁻¹-cong (g-inv _)) (f-inv x)

  inverseᵇ : Transitive ≈₁ → Transitive ≈₃ →
             Congruent ≈₂ ≈₃ g → Congruent ≈₂ ≈₁ f⁻¹ →
             Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₂ ≈₃ g g⁻¹ →
             Inverseᵇ ≈₁ ≈₃ (g ∘ f) (f⁻¹ ∘ g⁻¹)
  inverseᵇ trn₁ trn₃ g-cong f⁻¹-cong (f-invˡ , f-invʳ) (g-invˡ , g-invʳ) =
    inverseˡ trn₃ g-cong f-invˡ g-invˡ , inverseʳ trn₁ f⁻¹-cong f-invʳ g-invʳ
```


The one, general, proof serves whenever one wants to compose two bijections together. Amazing.
