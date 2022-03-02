% Compositional Correctness
% Sean Seefried
% Wed 02 Mar 2022

## Introduction

Proving programs correct is generally considered to be much harder than simply writing programs. There is quite a bit of evidence to support this position even though I will not go into it today. [Conal Elliott](http://conal.net) has a hunch about why this is. He thinks that main reason that proof is so difficultis that, most of the time, people attempt to prove properties about existing systems; systems that were designed in the absence of mathematical constraints.

If "proving only at the end" is the main reason for the difficulty of proof, then it may be the case that _simultaneously_ proving and writing our programs is the solution.

It is well-recognised that composing programs from simpler building blocks is a good way to construct larger programs. Another well-recognised "good thing" is the principle of _compositionality_ which says that when trying to reason about the composition of A and B, it is desirable that one should just be able to reason about A and B separately. [TODO: Find better formulations of the principle of compositionality].

What if one could compose programs _and_ their proofs simulatenously? This is eminently doable in Agda. Conal has coined a name for this technique: _compositional correctness_.

In this post we will look at an example of this in action.

## Proving at the end

Define `splitPermute`

[TODO: Reference previous blog post]

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute" }
splitPermute definition
```

Prove later:

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="inverse-proof" }
inverse-proof
```

Construct bijection:

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute-bijection-1" }
splitPermute-bijection
```
## Via _compositional correctness_

But there is a better way! The beautiful thing about bijections -- called `Inverse`s in Agda -- is that they have proofs bundled together with the programs. This is just what we need for _compositional correctness_.

I'll jump straight to the solution.

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="splitPermute-bijection-2" }
splitPermute-bijection
```

That's it. The function, its inverse and accompanying proofs of invertibility/congruence have all been defined _in a single line_.

In order to understand this code you will need to know about `+↔⊎` and `swap↔`. `+↔⊎` is defined in module `Data.Fin.Properties` and has the following definition:

```{ htmlDir="2022-02-24-permutations" module="Data.Sum.Properties" fun="+↔⊎" lines="2" }
+↔⊎ function definition
```

Function `swap↔` is something that I had to write myself even though all the building blocks were already present in `Data.Sum` and `Data.Sum.Properties`.

```{ htmlDir="2022-02-24-permutations" module="Permutations" delimeters="swap-bijection" }
swap-bijection
```

[TODO: Provide link to upcoming Agda repo]

### Why does this work?

The magic lies in the `∘-↔` operator defined in module `Function.Construct.Composition`. It's a synonym for `inverse` which is defined as:

```{ htmlDir="2022-02-24-permutations" module="Function.Construct.Composition" lineNumber="196" lines="8" }
inverse
```

One can further understand this code by looking at:

```{ htmlDir="2022-02-24-permutations" module="Function.Construct.Composition" lineNumber="56" lines="16" }
inverseᵇ and other definitions
```

The one, general, proof serves whenever one wants to compose two bijections together. Amazing.
