% Beefing up your mathematical structure constructively
% Sean Seefried
% Sat 19 Mar 2022

## Introduction

If you've spent any time studying Abstract Algebra or playing around with certain popular type classes in Haskell you'll have noticed that some mathematical structures contain within them other mathematical structures. In turn, these "larger" mathematical structure is often part of an even larger one.

As an example let's start with a _semigroup_. A _monoid_ is a semigroup that also has an identity element. A _commutative monoid_ is one for which the binary associative operator is also commutative. Further, a mathematical structure can have more than one sub-structure.  For instance, a _semiring_ consists of:

- a set for which `+` and `*` are defined
- two binary associative operators: `+` and `*`
- two distinguished elements: `0` and `1`
- `+` and `0` form a _commutative monoid_
- `*` and `1` form a _monoid_
- `*` distributes over `+`
- `0` is an _annihilator_ for `*`. i.e. for all `a` we have `a * 0 ≡ 0` and `0 * a ≡ 0`

Recently, I did some work on calculating timing delays in circuits. Conal Elliott introduced me to a very nice -- and a little quirky -- semiring. I'm going to call it the _delay semiring_ in the rest of this post.

In this semiring:
- the set is the integers (`ℤ`) augmented with a special value `⁻∞` that has the special property that it is less than all other values and that for all `a` we have `a + ⁻∞ ≡ ⁻∞` and `⁻∞ + a ≡ ⁻∞`
- the `+` operator of the semiring is the maximum operator (written as `⊔` in Agda)
- the `*` operator of the semiring is addition (`+`)
- the `0` value of the semiring is `⁻∞`
- the `1` value of the semiring is `0`.

Let's take a moment to informally convince ourselves that this is a semiring.
It should be relatively easy to convince yourself that `⊔`/`⁻∞` is a commutative monoid. It is well-known that `+`/`0` is a monoid on the integers. Next, we need convince ourselves that `+` distributes over `⊔`. i.e. that `a + (b ⊔ c) ≡ (a + b) ⊔ (a + c)`. This is true because if you add the same number to two integers it doesn't change which one is larger than the other. Lastly, `⁻∞` is an annihilator for `+` because we defined it that way.


``` { htmlDir="2022-03-14-delay-semiring" module="DelaySemiring" delimiters="ex1"}
```

```agda
ℤ⊔/⁻∞ a + (b ⊔ c) ≡ (a + b) ⊔ (a + c)
```
