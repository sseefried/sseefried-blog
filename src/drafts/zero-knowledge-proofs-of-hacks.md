% Zero knowledge proofs of hacks might level the playing field for White Hat hackers
% Sean Seefried
% Mon 13 June 2022

- Bug Bounties exist so that there is an incentive for Security Researchers (aka White Hat Hackers) and even Black Hat Hackers not to exploit a bug but instead responsibly disclose it.
- However, there are usually strict rules around the disclosure. If you disclose the bug prematurely you are usually disqualified from any payment and, worse, you might be open to legal attack. This is probably fair enough.
- But this puts the power back in the hands of the project owner. If they refuse to acknowledge the bug, or worse, fix the bug but not pay out to the White Hat, there's very little that White Hat can do.
- This is where I think Zero Knowledge Proofs could come in useful.
- Would it be acceptable to release a proof to the world that essentially said "I know how to hack this project but I'm not telling you how?". It could be even more specific it could say something like "given the bytecode deployed at these address I can drain this contract of funds greater than this particular amount".


Cons:
- it attracts attention to the project. Even knowing something is possible is a _big_ piece of knowledge. You could still argue that this is unacceptable behaviour.

What could we do about this problem?

- You could say "Out of these 100 projects I know how to hack 1 of them". Would that be reasonable. It would signify you have the knowledge to the project owner and the public simultaneously but make it infeasible to go hunting for the hack.

- I just had another idea. Perhaps you say "hey, it's one of these 128 projects". In a few days I'm releasing a proof that it's one of 64, then one of 32, etc. This gives people time to do something. e.g. users can pull their money out of the project.

- 0xDjango had an idea about creating a company like Immunefi that collects these ZKs for projects that aren't paying out.

- 0xDjango pointed out that it wouldn't be very nice to be one of the companies that randomly ended up in the diminishing "suspect" pool. Imagine being in the pool of 2?

- My first thought to solve this problem is to randomly throw in the other projects but then you just look at the intersection of the two sets. Lame. The two set operations we have just considered are subset and intersection. Is there a balance between the two? I can't think of one at the moment. It seems like a game of Guess Who no matter which way you think about it.

----

What I wrote on Discord:

> This would be leverage to get people to pay out
>
> If a PR campaign could be started and the community would accept this is a reasonable behaviour then perhaps white hat Bounty Hunters could get some power back.
>
> Because at the moment if you disclose anything it hurts your chances of getting a payout and, worse, probably opens you up to legal avenues of attack.
> I just had this idea BTW.
>
> Perhaps it's still too much to ask to be allowed to even say "I know how to hack this"
> Because it would draw attention to the project.
>
> Theoretically it should be possible to get quite specific in what your ZKP claims. e.g. "given the bytecode currently deployed at these addresses I know a way to exploit this for greater than $2M in damage (at token price on date X)"
>
> I don't know how to do this myself but I know that there's smart people out there who know who do this.

----

More stuff I wrote on Discord:

> Okay, I had some more ideas but they use existing tech.
> Here is something you can do to protect yourself in the situation where the project owner reads your submission, makes a fix based on it, but refuses to pay the bounty.
>
> 1. Make a git repo of your exploit and a fix.
> 2. Publicly post the hash of the latest commit to both Twitter and one of the blockchains if you want to get fancy. This will prove that the git repo with the exploit and the fix existed at a particular point in time.
> 3. Submit your exploit and fix to the project owner.
>
> Later, if they fix the code base without crediting you, you can do a diff of your git repo fix with their fix and publicly post the diff along with the hash proving that your fix existed at a particular point in time. The idea is that their fix and your fix should be quite close to each other. (Hmmm, what do you do about people who obfuscate their fix in order to avoid paying out?)
>
>There's one more detail I haven't worked out yet. They can always make the argument that they never received your fix. How do you prove you sent something and that it was received?
>
>A good way to get a proof of receipt would be for them to cryptographically sign a reply to your original email. However, how do you force them to do that?
