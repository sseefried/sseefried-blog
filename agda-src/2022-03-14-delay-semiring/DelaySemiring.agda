module DelaySemiring where

-- introduce HasSemiring ℕ+⁻∞ instance into scope
open import Data.Nat.Properties using (⊔-isCommutativeSemigroup; +-0-isMonoid; +-distrib-⊔)

open import SemiringExtras renaming (A⁺ to ℕ+⁻∞; A[_] to ℕ[_]; 0# to ⁻∞) public

open SemiringByAddingAnnihilatingZero
        ⊔-isCommutativeSemigroup +-0-isMonoid +-distrib-⊔
         public

open import HasAlgebra renaming (_+_ to _⊔_; _*_ to _+_) public

module _ where
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality using (_≡_; cong)
          renaming (isEquivalence to ≡-isEquivalence; refl to ≡-refl)
  open import Data.Nat using (ℕ) renaming (_≤_ to _≤ᴺ_)
  import Data.Nat.Properties as ℕ

  module _ (A : Set) where
    open import Relation.Binary.Structures (_≡_ {A = A}) public
    open import Relation.Binary.Core public
    open import Relation.Binary.Definitions public
    open import Relation.Binary.Bundles public


  open import Data.Sum
  open IsTotalPreorder ⦃ … ⦄

  instance
    _ : IsTotalPreorder ℕ _≤ᴺ_
    _ = ℕ.≤-isTotalPreorder

  data _≤_ : ℕ+⁻∞ → ℕ+⁻∞ → Set where
    ⁻∞≤n : {n : ℕ+⁻∞} → ⁻∞ ≤ n
    ℕ≤ℕ  : {m n : ℕ} → m ≤ᴺ n → ℕ[ m ] ≤ ℕ[ n ]

  _≥_ : ℕ+⁻∞ → ℕ+⁻∞ → Set
  a ≥ b = b ≤ a

  ≤-isPreorder : IsPreorder ℕ+⁻∞ _≤_
  ≤-isPreorder =
    record
      { isEquivalence = ≡-isEquivalence
      ; reflexive = λ { {⁻∞} ≡-refl → ⁻∞≤n ; {ℕ[ _ ]} ≡-refl → ℕ≤ℕ (reflexive ℕ ≡-refl) }
      ; trans = λ { ⁻∞≤n _ → ⁻∞≤n
                  ; (ℕ≤ℕ m≤ᴬn) (ℕ≤ℕ n≤ᴬp) → ℕ≤ℕ (trans ℕ m≤ᴬn n≤ᴬp)
                  }
      }

  ≤-total : Total _≤_
  ≤-total ⁻∞ _ = inj₁ ⁻∞≤n
  ≤-total _ ⁻∞ = inj₂ ⁻∞≤n
  ≤-total (ℕ[ i ]) (ℕ[ j ]) = map ℕ≤ℕ ℕ≤ℕ (total i j)

  ≤-isTotalPreorder : IsTotalPreorder ℕ+⁻∞ _≤_
  ≤-isTotalPreorder = record
    { isPreorder = ≤-isPreorder
    ; total = ≤-total
    }

  ≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder =
    record
      { Carrier = ℕ+⁻∞
      ; _≈_     = _≡_
      ; _≲_     = _≤_
      ; isTotalPreorder = ≤-isTotalPreorder
      }

  ≤-isPartialOrder : IsPartialOrder ℕ+⁻∞ _≤_
  ≤-isPartialOrder =
    record
      { isPreorder = ≤-isPreorder
      ; antisym    = λ { ⁻∞≤n ⁻∞≤n → ≡-refl ; (ℕ≤ℕ i≤j) (ℕ≤ℕ j≤i) → cong ℕ[_] (ℕ.≤-antisym i≤j j≤i) }
      }

  ≤-poset : Poset 0ℓ 0ℓ 0ℓ
  ≤-poset =
    record
      { Carrier = ℕ+⁻∞
      ; _≈_ = _≡_
      ; _≤_ = _≤_
      ; isPartialOrder = ≤-isPartialOrder }

  import Algebra.Construct.NaturalChoice.MaxOp ℕ.⊔-operator as ℕ-MaxOp
  open import Algebra.Construct.NaturalChoice.Base using (MaxOperator)

  i≤j⇒i⊔j≡j : {i j : ℕ+⁻∞} → i ≤ j → i ⊔ j ≡ j
  i≤j⇒i⊔j≡j ⁻∞≤n       = ≡-refl
  i≤j⇒i⊔j≡j (ℕ≤ℕ x≤y)  = cong ℕ[_] (MaxOperator.x≤y⇒x⊔y≈y ℕ.⊔-operator x≤y)

  i≥j⇒i⊔j≡i : {i j : ℕ+⁻∞} → i ≥ j → i ⊔ j ≡ i
  i≥j⇒i⊔j≡i {i} {j} i≤j rewrite +-comm {x = i} {j} = i≤j⇒i⊔j≡j {j} {i} i≤j

  ⊔-operator : MaxOperator ≤-totalPreorder
  ⊔-operator = record
    { _⊔_ = _⊔_
    ; x≤y⇒x⊔y≈y = i≤j⇒i⊔j≡j
    ; x≥y⇒x⊔y≈x = i≥j⇒i⊔j≡i
    }

  open import Algebra.Construct.NaturalChoice.MaxOp ⊔-operator public

  +-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤ ⁻∞ _ = ⁻∞≤n
  +-monoʳ-≤ ℕ[ m ] ⁻∞≤n  = ⁻∞≤n
  +-monoʳ-≤ ℕ[ m ] (ℕ≤ℕ x≤y) = ℕ≤ℕ (ℕ.+-monoʳ-≤ m x≤y)

--
-- Examples
--

module private-examples where
  open import Relation.Binary.PropositionalEquality
  open import Level using (0ℓ)

--pandoc-begin ex1
  ex1 : ∀ n → n ⊔ ⁻∞ ≡ ℕ[ 0 ] + n
  ex1 n =
      begin
        n ⊔ ⁻∞       ≡⟨ HasAlgebra.+-identityʳ ⟩
        n            ≡⟨ sym (HasAlgebra.*-identityˡ) ⟩
        ℕ[ 0 ] + n
      ∎
    where open ≡-Reasoning
--pandoc-end ex1

  ex2 : ∀ n → n + ℕ[ 0 ] ≡ n
  ex2 n = HasAlgebra.*-identityʳ {x = n}
