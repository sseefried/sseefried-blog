% Compositional Correctness
% Sean Seefried
% Thu 03 Mar 2022

## Introduction

Writing and proving programs correct is generally considered to be much harder than writing them alone. There is quite a bit of evidence to support this position but I will not cover it in this post. [Conal Elliott](http://conal.net) has a hunch about why proving programs correct is so much more difficult. He thinks the main reason is that -- most of the time --  people attempt to prove properties about existing systems; systems designed in the absence of mathematical constraints.

If "proving at the end" is the main reason for the difficulty of proof, then it may be the case that an approach where we _simultaneously_ write _and_ prove is the solution.

It is a well-recognised principle that composing programs from simpler building blocks is a good way to construct larger programs. Another well-recognised "good thing" is the [principle of compositionality](https://en.wikipedia.org/wiki/Principle_of_compositionality) which states that when trying to reason about the composition of A and B, it is desirable that the meaning of the composition is determined by the meanings of A, B and the rules used to combine them. It is undesirable (and non-compositional) in the case where reasoning about A and B together either

- can't be done by reasoning about A and B independently, or
- is significantly more complicated than reasoning about A and B in isolation

What if we were to adopt a discipline where programs _and_ their proofs were composed simultaneously? This style of programming is well-supported in dependently typed languages such as Agda, Coq, and Idris. Conal has even coined a name for this technique: _compositional correctness_.

In this post we will look at an example of _compositional correctness_ in action.

## Proving at the end

But first, we'll take a look at constructing a program and then only "proving at the end".

In my [last post](./proving-a-more-general-theorem-is-often-easier.md) we define a function called `splitPermute` as follows:

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute" }
splitPermute definition
```

We were able to prove that `splitPermute n` was the inverse of `splitPermute m`, for a given `m + n : ℕ` as follows:

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="inverse-proof" }
inverse-proof
```

We then constructed a bijection -- called an `Inverse` in Agda -- as follows. This packages up a program with proofs of invertibility.

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute-bijection-1" }
splitPermute-bijection
```
## Construction via _compositional correctness_

But there is a better way! The beautiful thing about bijections is that their proofs are bundled together with the program. This is just what we need for _compositional correctness_.

Let's see how this is done for `splitPermute`.

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute-bijection-2" }
splitPermute-bijection
```

That's it! The function, its inverse and accompanying proofs of invertibility have all been defined _in a single line_.

In order to understand this code you will need to study the definitions of `+↔⊎` and `swap↔`. `+↔⊎` is defined in module `Data.Fin.Properties` and has the following definition:

```{ htmlDir="2022-02-24-permutations" module="Data.Fin.Properties" fun="+↔⊎" lines="2" }
+↔⊎ function definition
```

Function `swap↔` is something that I had to write myself even though all the building blocks were already present in `Data.Sum` and `Data.Sum.Properties`.

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="swap-bijection" }
swap-bijection
```

I submitted a PR to the GitHub `agda-stdlib` repository which added this function. It has now been [incorporated](https://github.com/agda/agda-stdlib/commit/9bf16e21f0fcdefd9200d4f368bbeaee67b84c75) and will appear in a future release of the Agda Standard Library.


### Compositional correctness via the bijection composition operator `∘-↔`

The magic of this approach is in the `∘-↔` operator which is defined in module `Function.Construct.Composition`. It is a synonym for function `inverse` which is defined as:

```{ htmlDir="2022-02-24-permutations" module="Function.Construct.Composition" lineNumber="196" lines="8" }
inverse
```

One can further understand this code by looking at:

```{ htmlDir="2022-02-24-permutations" module="Function.Construct.Composition" lineNumber="56" lines="16" }
inverseᵇ and other definitions
```

As you can see a single, general, proof serves whenever one wants to compose two bijections together.

If we compare the "prove at the end" with the compositional correctness approach, we see that in the "prove at the end" approach we had to carefully apply three different invertibility proofs (in order):

1. `splitAt-join`
2. `swap-involutive`
3. `join-splitAt`

However, by using the approach of compositional correctness, we actually applied `inverseᵇ` (under the hood) three times, and the application was implicitly done with each application of the `∘-↔` operator.

## Conclusion

A style of programming coined by Conal Elliott and called _compositional correctness_ can be used to reduce the cost of proving one's programs correct. In the example we considered, "proving at the end" involved carefully selecting _specific_ theorems while _compositional correctness_ used a _general_ theorem (at three specific types) to achieve its goals.

It will remain to be seen whether compositional correctness radically reduces the difficulty of proving program correctness, but it is a very promising candidate.
