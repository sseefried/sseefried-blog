module Permutations where

module +1-mod-n-module where
  open import Data.Nat
  import Data.Nat as ℕ
  import Data.Nat.Properties as ℕ
  open import Data.Fin renaming (Fin to 𝔽)
  open import Data.Fin.Properties hiding (setoid)
  open import Function.Inverse
  open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; cong; module ≡-Reasoning)
  open import Relation.Nullary
  open import Function.LeftInverse
  open import Function.Equality using (_⟶_)
  open import Level using (0ℓ)
  open import Relation.Binary.Bundles
  open import Data.Product

--pandoc-begin Perm
  Perm : ℕ → Set
  Perm n = 𝔽 n ↔ 𝔽 n
--pandoc-end Perm

--pandoc-begin plus-one-mod-n
  +1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
  +1-mod-n {ℕ.suc n} m with n ℕ.≟ toℕ m
  ... | no m≢n  = suc (lower₁ m m≢n)
  ... | yes _ = zero
--pandoc-end plus-one-mod-n

--pandoc-begin minus-one-mod-n
  -1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
  -1-mod-n {ℕ.suc n} zero = fromℕ n
  -1-mod-n {ℕ.suc n} (suc m) = inject₁ m
--pandoc-end minus-one-mod-n

--pandoc-begin ugly-left-inverse-proof
  i≡j⇒j<i+1 : ∀ {i j } → i ≡ j → j ℕ.< ℕ.suc i
  i≡j⇒j<i+1 {i} {j} i≡j =
    begin
      ℕ.suc j
    ≡⟨ cong ℕ.suc (≡-sym i≡j) ⟩
      ℕ.suc i
    ∎
    where
      open Relation.Binary.PropositionalEquality renaming (sym to ≡-sym)
      open ℕ.≤-Reasoning

  open ≡-Reasoning

  left-inverse′ : (n : ℕ) → (x : 𝔽 n) → -1-mod-n (+1-mod-n x) ≡ x
  left-inverse′ ℕ.zero ()
  left-inverse′ (ℕ.suc ℕ.zero) zero = refl
  left-inverse′ (ℕ.suc (ℕ.suc n′)) x
              with ℕ.suc n′ ℕ.≟ toℕ x
  ...  | no n+1≢x with x
  ...               | zero = refl
  ...               | suc x =
      begin
        -1-mod-n (suc (lower₁ (suc x) n+1≢x))
      ≡⟨⟩
        inject₁ (lower₁ (suc x) n+1≢x)
      ≡⟨  inject₁-lower₁ (suc x) n+1≢x ⟩
        suc x
      ∎
  left-inverse′ (ℕ.suc (ℕ.suc n)) x
       | yes n+1≡x =
     begin
       -1-mod-n zero
     ≡⟨⟩
       fromℕ (ℕ.suc n)
     ≡⟨ fromℕ-def (ℕ.suc n) ⟩
       fromℕ< n+1<n+2
     ≡⟨ fromℕ<-cong (ℕ.suc n) (toℕ x) n+1≡x n+1<n+2 (i≡j⇒j<i+1 n+1≡x) ⟩
        fromℕ< (i≡j⇒j<i+1 n+1≡x )
     ≡⟨ fromℕ<-toℕ x (i≡j⇒j<i+1 n+1≡x)  ⟩
       x
     ∎
     where
       n+1<n+2 : ℕ.suc n ℕ.< ℕ.suc (ℕ.suc n)
       n+1<n+2 = ℕ.s≤s (ℕ.s≤s (ℕ.≤-reflexive refl))
--pandoc-end ugly-left-inverse-proof

module RewriteOfJoin where
  import Data.Nat as ℕ
  open import Data.Fin renaming (join to join′)
  open import Data.Sum

  -- A more direct definition of `join`
  join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
--pandoc-begin join-direct
  join m n (inj₁ x) = inject+ n x
  join m n (inj₂ y) = raise {n} m y
--pandoc-end join-direct

module SplitPermute1 where

  open import Data.Nat using (ℕ; _+_)
  open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)
  open import Data.Fin.Properties hiding (setoid)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)
  open import Data.Sum
  open import Data.Sum.Properties
  open import Function
  open import Function.Bundles
  open import Level using (Level)

--pandoc-begin splitPermute
  splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m + n) → 𝔽 (n + m))
  splitPermute m {n} = join n m ∘ swap ∘ splitAt m
--pandoc-end splitPermute

--pandoc-begin composition-cong
  cong-[_]∘⟨_⟩∘[_] :
    {a : Level} {A′ A B B′ : Set a}
    → (h : B → B′)
    → {f g : A → B}
    → f ≗ g
    → (h′ : A′ → A)
    → h ∘ f ∘ h′ ≗ h ∘ g ∘ h′
  cong-[_]∘⟨_⟩∘[_] h {f} {g} f≗g h′ = λ x → cong h (f≗g (h′ x))
    where
      open Relation.Binary.PropositionalEquality using (cong)
--pandoc-end composition-cong

--pandoc-begin inverse-proof
  inverse : {m n : ℕ} → splitPermute n ∘ splitPermute m ≗ id
  inverse {m} {n} =
    begin
      (splitPermute n ∘ splitPermute m)
    ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n) ∘ (join n m ∘ swap ∘ splitAt m)
    ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m)
    ≈⟨ cong-[ join m n ∘ swap ]∘⟨ splitAt-join n m ⟩∘[ swap ∘ splitAt m ] ⟩
--pandoc-begin inverse-proof-snippet-1
      (join m n ∘ swap ∘ swap ∘ splitAt m)
    ≈⟨ cong-[ join m n ]∘⟨ swap-involutive ⟩∘[ splitAt m ] ⟩
      (join m n ∘ splitAt m)
--pandoc-end inverse-proof-snippet-1
    ≈⟨ join-splitAt m n ⟩
      id
    ∎
    where
      open import Relation.Binary.PropositionalEquality
      open import Relation.Binary.Reasoning.Setoid (𝔽 (m + n) →-setoid 𝔽 (m + n))
--pandoc-end inverse-proof

--pandoc-begin splitPermute-bijection-1
  splitPermute↔ : (m : ℕ) {n : ℕ} → (𝔽 (m + n) ↔ 𝔽 (n + m))
  splitPermute↔ m {n} = mk↔′ (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n})
--pandoc-end splitPermute-bijection-1

module SplitPermuteWithConstructiveCorrectness where

  open import Data.Nat using (ℕ; _+_)
  open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)
  open import Data.Fin.Properties hiding (setoid)
  open import Function.Construct.Composition hiding (inverse)
  open import Function.Construct.Symmetry using (sym-↔)
  open import Function using (mk↔′; _↔_)
  open import Function.Bundles using (Inverse)
  open import Data.Sum
  open import Data.Sum.Properties
  open Inverse

--pandoc-begin swap-bijection
  swap↔ : ∀ {a b} {A : Set a} {B : Set b} →  (A ⊎ B) ↔ (B ⊎ A)
  swap↔ {a} {b} {A} {B} = mk↔′ swap swap swap-involutive swap-involutive
--pandoc-end swap-bijection

--pandoc-begin splitPermute-bijection-2
  splitPermute↔ : (m : ℕ) {n : ℕ} → 𝔽 (m + n) ↔ 𝔽 (n + m)
  splitPermute↔ m {n} = (+↔⊎ {m} {n} ∘-↔ swap↔) ∘-↔ sym-↔ +↔⊎
--pandoc-end splitPermute-bijection-2
