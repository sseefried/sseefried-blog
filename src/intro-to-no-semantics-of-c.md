% Introducing a series of posts on the semantics of C
% Sean Seefried
% Thu 06 Jan 2022

About a month ago I set out to write a post about Undefined Behaviour in C. The aim was to show that C does not have a well-defined semantics, and why it might be important that you should use a language that _does_ have a semantics that is well-defined. I also wanted to point out that we should really care about this since so much important software is written in C (e.g. the Linux kernel). I wanted to show that our computing foundations are built on, if not quicksand, marshy ground at the very least.

I learned a lot in the process, and I still have a lot more to learn. Some of my preconceptions were confirmed but others weren't. I learned that there is a very diverse set of opinions in the C community on this topic. But I learned enough to realise that capturing all the insights in one blog post is not feasible since

- I would never finish it
- even if I did it would be too long for one post

Instead, I've decided to write a series of posts each of which will address one of the following themes:

1. Demonstrating that the semantics of C is informal, imprecise and open to interpretation.

2. Presenting diverse views about the semantics of C from the C community along with my own commentary.

3. Presenting my own views on the pitfalls of having an ill-defined semantics and why using a language with a precise semantics is beneficial, even necessary.

I refer to these posts collectively as the _No Semantics of C Series_ and links to each post appear below. This list will be updated as each post is written.
