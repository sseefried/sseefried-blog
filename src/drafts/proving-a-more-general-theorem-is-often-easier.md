% Proving a more general theorem is often easier
% Sean Seefried
% Fri 18 Feb 2022

## Introduction

A common approach I follow when programming -- and I'm not proving the correctness of those programs -- is to "generalise from the specific". While trying to solve a programming problem, I find it easier to work with more concrete concepts first and only later to generalise my solution.

A simple of example of this might be that I'll write a function to sort a list of integers before going on to generalise it to sort a list of anything that can be ordered.

But I've discovered something counter-intuitive. When proof is involved, this can actually be harder. Proofs on specific structures can actually be a lot harder than proofs on more general structures. If this is true in general then it makes sense to do the hard work of generalising one's programs up-front because it will making proving them correct _easier_. Further I suspect the combined work of a) writing the program and proving it correct will be less than b) writing a specific program, trying to prove it, failing, generalising the program and finally proving it correct.

Even thought this seems completely counter-intuitive I suspect it's just a consequence of the fact that general structures, lacking concreteness, are _defined by_ their mathematical properties and these mathematical properties are useful in proving correctness.

In this post I'd like to show you an example of a specific program that was hard to prove correct but became much easier once I had generalised the program.

## Bijections that permute a finite set

I defined a _permutation_ as a bijection from `Fin n` to `Fin n` for some `n`. For convenience I renamed `Fin` to `𝔽` because I really value conciseness and it has echoes of `Data.Nat`'s `ℕ`.

```agda
Perm : ℕ → Set
Perm n = 𝔽 n ↔ 𝔽 n
```

In Agda a bijection is constructed from:

- a function going in the forward direction: `f`
- a function going in the backwards direction: `f⁻¹`
- a proof that `f⁻¹ ∘ f ≡ id` i.e. that `f⁻¹` is a left-inverse of `f`
- a proof that `f ∘ f⁻¹ ≡ id` i.e. that `f⁻¹` is a right-inverse of `f`

## Introducing `+1-mod-n` and `-1-mod-n`

I thought I'd play around with a very simple permutation that, in the forward direction, evaluates to the successor of its input modulo `n`.

```agda
+1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
+1-mod-n {ℕ.suc n} m with n ℕ.≟ toℕ m
... | no m≢n  = suc (lower₁ m m≢n)
... | yes _ = zero
```

And here is its inverse:

```agda
-1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
-1-mod-n {ℕ.suc n} zero = fromℕ n
-1-mod-n {ℕ.suc n} (suc m) = inject₁ m
```

I liked the definition for `-1-mod-n` much better than the `+1-mod-n`, but couldn't think of an alternative way to define the latter. I then got stuck into trying to prove that `-1-mod-n` is the left-inverse of `+1-mod-n`.

The proof took me many hours but eventually I came up with the following. It's a very ugly proof and the only reason I have posted it here is so that you can have an "ugh"-reaction.

```agda
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
```

I also tried to prove that `-1-mod-n` was the right inverse of `+1-mod-n` but got stuck almost straight away and gave up.

## A generalisation of the pattern of permutation

If you look carefully there is an obvious generalisation of the pattern of permutation staring us in the face. Imagine all the possible values of `Fin n` written down, in order, as a list:

```
[ 0, 1, ..., n - 1 ]
```

Now imagine _splitting_ this list into two sub-lists:

```
[ 0, 1, ... n - 2 ] [ n - 1]
```

Now _swap_ the two sub-lists:

```
[n - 1] [ 0, 1, ... n - 2 ]
```

Now _join_ them again:

```
[ n - 1, 0, 1, ... n - 2 ]
```

Now, call this list `P` and imagine that it is indexed by the values of `𝔽 n`. We find that `P[i] ≡ +1-mod-n i` for all `i ∈ 𝔽 n`.

It turns out that there are a number of functions in modules `Data.Fin` and `Data.Sum` that do something very similar to the split-swap-join exercise we just went through above.

The signatures of these functions are:

```agda
splitAt : ∀ m {n} → Fin (m ℕ.+ n) → Fin m ⊎ Fin n
swap : A ⊎ B → B ⊎ A
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
```

The behaviour of `join` is worth looking at in more detail.

```agda
join : ∀ m n → Fin m ⊎ Fin n → Fin (m ℕ.+ n)
join m n = [ inject+ n , raise {n} m ]′
```

where `[_,_]′` is defined as follows:

```agda
[ f , g ]′ (inj₁ x) = f x
[ f , g ]′ (inj₂ y) = g y
```

Simplifying these means that `join` could be rewritten as:

```agda
join m n (inj₁ x) = inject+ n x
join m n (inj₂ y) = raise {n} m y
```

The type signatures of the two functions on the RHS of the definition above are:

```agda
inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)
raise : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
```

Function `inject+` takes a `Fin m` and "injects" it into the `Fin (m ℕ.+ n)` type without changing the structure of the value. e.g. For value `suc (suc zero) : Fin 3`, `inject+ (suc (suc zero))` evaluates to `suc (suc zero) : Fin 5` for `m = 3` and `n = 2`.

Function `raise` is a little different to `inject+`. It adds `n` to its argument while increasing the size of the type to `Fin (n ℕ.+ m)`. e.g. `raise {3} 2 (suc (suc zero))` evaluates to `suc (suc (suc (suc zero))) : Fin 5`.

We can now now define a function called `splitPermute` that performs the split-swap-join process that I described earlier.

```agda
splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m + n) → 𝔽 (n + m))
splitPermute m {n} = join n m ∘ swap ∘ splitAt m
```

One really nice thing about this function is that for a given `m + n` the inverse of `splitPermute m` is `splitPermute n`.

Remember function `+1-mod-n` from earlier?  It is the special case of `splitPermute` where `n = 1`.

Yet the proof that `splitPermute n` is the left inverse of `splitPermute m` is _much simpler_ than the proof that `-1-mod-n` is the left inverse of `+1-mod-n`.

The make use of the following three theorems from `Data.Fin.Properties` and `Data.Sum.Properties`

```agda
splitAt-join : ∀ m n i → splitAt m (join m n i) ≡ i
swap-involutive : swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
join-splitAt : join-splitAt : ∀ m n i → join m n (splitAt m i) ≡ i
```

Here is the proof!

```agda
  inverse : {m n : ℕ} → splitPermute n ∘ splitPermute m ≗ id
  inverse {m} {n} =
    begin
      (splitPermute n ∘ splitPermute m)
    ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n) ∘ (join n m ∘ swap ∘ splitAt m)
    ≡⟨⟩
      (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m)
    ≈⟨ cong-[ join m n ∘ swap ]∘⟨ splitAt-join n m ⟩∘[ swap ∘ splitAt m ] ⟩
      (join m n ∘ swap ∘ swap ∘ splitAt m)
    ≈⟨ cong-[ join m n ]∘⟨ swap-involutive ⟩∘[ splitAt m ] ⟩
      (join m n ∘ splitAt m)
    ≈⟨ join-splitAt m n ⟩
      id
    ∎
    where
      open import Relation.Binary.PropositionalEquality
      open import Relation.Binary.Reasoning.Setoid (𝔽 (m + n) →-setoid 𝔽 (m + n))
```

If you're confused about the use of `cong-[_]∘⟨_⟩∘[_]` above. It's just a nice helper function I wrote to help with _setoid_ reasoning on _extensional equality_ (`_≗_`). It is defined as follows:

```agda
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
```

Agda's ability to define mixfix operators using the `_` character really shon here. See how nice the fragment below looks? The parts between the square brackets remain untouched while the law between the angle brackets (`⟨⟩`) applies a law, in this case: `swap-involutive`.

 ```agda
     (join m n ∘ swap ∘ swap ∘ splitAt m)
    ≈⟨ cong-[ join m n ]∘⟨ swap-involutive ⟩∘[ splitAt m ] ⟩
      (join m n ∘ splitAt m)
```

## Conclusion

In this post I showed you how proving a theorem on a more general formulation of a problem often turns out to be easier than doing it for a specific case. In this particular case you may argue that the specific case could have been defined in terms of `splitAt`, `swap` and `join` _and you'd be correct_. However, I simply didn't spot that at the time. It was only by thinking about what the general pattern of permutation was that allowed me to see that these functions even should be used.

One is likely to generalise a program once a specific solution is found, but proving things on general programs is often easier. Given this is true it makes sense to do the work, up-front, of generalising when programming in a language like Agda.
