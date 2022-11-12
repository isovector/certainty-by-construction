It was almost ten years ago when I stumbled across the idea that, in order to
truly understand something, one should write themselves a textbook to really
flesh out the concepts. The reasoning, it goes, is that when you're just forced
to articulate something from the ground up, the holes in your understanding
become immediately obvious. The goal, as Richard Feynman says, is "the first
principle is that you must not fool yourself and you are the easiest person to
fool."

The first textbook project I ever attempted in earnest was one on category
theory, an alternative foundation for mathematics than the more traditional set
theory. Category theory has much to recommend it; while set theory is very good
at raw get-the-answer-by-any-means-necessary approaches, category theory instead
gives good theoretical underpinnings to concepts like abstraction and
composition. The argument I'd heard somewhere was that doing math in sets was
like writing programs in assembly code, while doing it in categories was
comparative to writing them in a language like Haskell.

While writing a textbook was indeed helpful at identifying holes in my
understanding, it was never a particularly good tool for *building* that
understanding. My mathematics education is rather spotty --- I was good at
"running the maze" in school, which is to say, I could reliably compute answers.
At university I received an engineering degree, which required lots more running
of the maze, but I did horrendously in all of my math qua math courses. I had
grown up writing software, and it felt extraordinarily vulnerable to need to
write the technical solutions that math requires without having some sort of
compiler, or even runtime, to help troubleshoot my proofs. As a self-taught
programmer, I had developed a bad habit of brute-forcing my way to working
programs. My algorithm for this was as follows:

1. write a program that seems to make sense
2. run it and pray that it works
3. insert some print statements to try to observe the failure
4. make random changes
5. go back to 2

Depending on the programming language involved, this can be an extremely tight
feedback loop. But when it came to mathematics, this algorithm simply no longer
worked. It's meaningless to "run" a proof. And furthermore, as a
non-mathematician thrust into the domain, it's unclear even what are the
primitive statements of proofs. Which steps did I need to justify? How could I
know when I was done? When is a proof sufficiently convincing?

At least in university, the answer to that last question is "when you get 100%
on the assignment." In a very real sense, the feedback algorithm for mathematics
is this:

1. write the proof
2. submit the assignment
3. wait for it to be marked
4. tweak the bits that have red underlines
5. go back to 2

Of course, this algorithm requires some sort of mythical TA with infinite time
and understanding, who will continually mark your homework until you're
satisfied with it. You might not get the grade, but with perseverance, you'll
eventually intuit the decision procedure that allows a theorem to pass through
without any red underlines. I suppose this is how anyone learns anything, but
the feedback cycle is excruciatingly slow.

Perhaps out of tenaciousness and math-envy more than anything else, I managed to
keep at my category theory goal for seven years. I would pick up a new textbook
every few years, push through it, get slightly further than the last time, and
then bounce off anew. As you can imagine, the process was extremely slow-going,
but I did seem to be making sense of it. Things sped up immensely when I made
friends with kind, patient people who knew category theory, who would reliably
answer my questions and help when I got stuck.

What a godsend! Having kind, patient friends sped up the feedback algorithm for
mathematics by several orders of magnitude, from "wait until the next time I
pick up a category theory textbook and identify some mistakes in my
understanding elucidated by time" to "ask a friend and get a response back in
less than an hour." Amazing stuff.

I don't know exactly how I got onto the proof-assistant train, but at some
point, one of those kind, patient friends introduced me to Lean. Lean is a
programming language for doing mathematics, and it gave me a taste of what was
possible. The selling point for me was that it had a *standard library of
mathematical theorems.* As a software guy, I know how to push programming
knowledge into my brain. You bite off a module of the standard library at a
time, learning what's there, inlining definitions, and reading code. If you ever
need to check your understanding, you just code up something that seems to make
sense and see if the compiler accepts it. Now, as they say, we were cooking with
gas.

Lean and I never really gelled, on an aesthetic level. Lean takes a lot of ideas
from C++, which is a hard language for even a mother to love. But, what was
worse, was that I was reliably proving theorems without knowing what I was
doing. A huge amount of mathematical reasoning was seemingly implemented inside
the Lean compiler itself, meaning one must also understand the meta-theory
provided by the compiler in order to reliably understand the code. You see, Lean
is really two languages, one at the level of expressions and values, and another
at the proof-rewriting level. While it allows you to work with proofs, they're
operated on in a context completely outside of my understanding, and I quickly
fell out of favor with Lean.

But now I had a taste of what was possible, and I tried Agda instead, on the
advice of quite a few smart people. Agda was everything I was hoping Lean would
be; a fleshed out mathematical standard library, but in a language that felt
much more like home. And furthermore, the magical proof machinery that Agda
offered was all just library code!

Learning Agda has been slow going, and I chipped away at it for a year in the
context of trying to prove things not about mathematics, but about my own
programs. It's nice, for example, to prove your algorithm always gets the right
answer, and to not need to rely on a bevy of tests that hopefully cover the
input space (but how would you ever know?).

In the meantime, I had also been experimenting with writing category theory in
Agda. That is, I picked a new textbook, and this time, coded up all of the
definitions and theorems in Agda, as well as formalized my answers to the
exercises. WOW! What a difference this made! All of a sudden I had the feedback
mechanism for mathematics that I'd always wanted. I could get the red underlines
on unconvincing (or wrong) parts of my argument automatically --- on the order
of seconds!

Truly this was a marvelous technology.

When feedback becomes instant, tedious chores turn into games. I found myself
learning mathematics into the late evenings on weekends. I found myself redoing
theorems I'd already proved, trying to find ways of making them prettier, or
more elegant, or more concise, or what have you. I've made more progress in
category theory in the last six months than I had in a decade.

The idea to write this book came a few months later, when some friends of mine
had an idea about generalizing some well-established applied mathematics around
game theory. I didn't know anything about the domain, but thought it might be
fun, and that I could tag along, perhaps being helpful on formalizing some of
their insights. What I took away from this experience was that in all of my
practice, I'd learned a great deal about Agda, much more than I was aware.

I came away with the insight that there are a lot more people out there like me:
people who want to be better at mathematics but don't quite know how to get
there. People who are technically minded and have keen domain knowledge, but are
lacking the *proof* side of things. And after all, what is mathematics without
proof?

So we come now to this book. This book is the textbook I ended up writing, not
to teach myself category theory, but instead to teach myself mathematics. In the
process of explaining the techniques, and the necessity of linearizing the
narrative, I've been forced to grapple with my understanding of mathematics, and
it has become very clear in the places I was fooling myself. Of course, this
book is itself an Agda document, meaning it is a living, breathing, and most
importantly, *fully type-checking* Agda library --- meaning it comes with the
guarantee that I have told no lies, at least, none mathematically. I am by no
means an expert in this field, but have stumbled across a fantastic method of
learning and teaching mathematics.

This textbook is the book I wish I had found ten years ago. It would have saved
me a great deal of wasted effort and false starts. I hope it can save you the
same. Good luck, godspeed, and welcome aboard.

