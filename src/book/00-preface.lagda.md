# Preface

It was almost ten years ago when I stumbled across the idea that in order to
truly understand something, one should write themselves a textbook to really
flesh out the concepts. The reasoning, it goes, is that when you're just forced
to articulate something from the ground up, the holes in your understanding
become immediately obvious. As Richard Feynman says, "the first principle is
that you must not fool yourself and you are the easiest person to fool."

The first textbook project I ever attempted in earnest was one on category
theory, an alternative foundation for mathematics, as opposed its more
traditional set theoretic foundation. Category theory has much to recommend it;
while set theory is very good at get-the-answer-by-any-means-necessary sorts of
approaches, category theory instead gives good theoretical underpinnings to
otherwise-nebulous concepts like "abstraction" and "composition." The argument
I'd heard somewhere was that doing math in sets was like writing programs in
assembly code, while doing it in categories was comparative to writing them in a
modern programming language.

While writing a textbook was indeed helpful at identifying holes in my
understanding, it was never a particularly good tool for *building* that
understanding in the first place. My mathematics education is rather spotty---I
was good at "running the maze" in school, which is to say, I could reliably
compute answers. At university I received an engineering degree, which required
lots more running of the maze, but I did horrendously in all of my *actual* math
courses. I had grown up writing software, and it felt extraordinarily vulnerable
to need to write the technical solutions required by mathematics, without having
tooling to help me. I was looking for some sort of compiler or runtime to help
troubleshoot my proofs. As a self-taught programmer, I had developed a bad habit
of brute-forcing my way to working programs. My algorithm for this was as
follows:

1. write a program that seems to make sense
2. run it and pray that it works
3. insert some print statements to try to observe the failure
4. make random changes
5. go back to 2

Depending on the programming language involved, this can be an extremely tight
feedback loop. But when it came to mathematics, the algorithm becomes much less
effective. Not only is it meaningless to "run" a proof, but also as a
non-mathematician thrust into the domain, I found it unclear what even
constituted a proof. Which steps did I need to justify? How could I know when I
was done? When is a proof sufficiently convincing?

At least in university, the answer to that last question is "when you get 100%
on the assignment." In a very real sense, the feedback algorithm for mathematics
is this:

1. write the proof
2. submit the assignment
3. wait for it to be marked
4. tweak the bits that have red underlines
5. go back to 2

Of course, this algorithm requires some sort of mythical teaching assistant with
infinite time and understanding, who will continually mark your homework until
you're satisfied with it. You might not be done in time to get the grade, but
with perseverance, you'll eventually find enlightenment---intuiting the decision
procedure that allows a theorem to pass through without any red underlines. I
suppose this is how anyone learns anything, but the feedback cycle is
excruciatingly slow.

Perhaps out of tenaciousness and math-envy more than anything else, I managed to
keep at my category theory goal for seven years. I would pick up a new textbook
every few years, push through it, get slightly further than the last time, and
then bounce off anew. The process was extremely slow-going, but I did seem to be
making sense of it. Things sped up immensely when I made friends with kind,
patient people who knew category theory, who would reliably answer my questions
and help when I got stuck.

What a godsend! Having kind, patient friends sped up the feedback algorithm for
mathematics by several orders of magnitude, from "wait until the next time I
pick up a category theory textbook and identify some mistakes in my
understanding elucidated by time" to "ask a friend and get a response back in
less than an hour." Amazing stuff.

At some point, one of those kind, patient friends introduced me to proof
assistants. Proof assistants are essentially programming languages meant for
doing mathematics, and stumbling across them gave me a taste of what was
possible. The selling point is that these languages come with a *standard
library of mathematical theorems.* As a software guy, I know how to push
programming knowledge into my brain. You bite off one module of the standard
library at a time, learning what's there, inlining definitions, and reading
code. If you ever need to check your understanding, you just code up something
that seems to make sense and see if the compiler accepts it. Now, as they say,
I was cooking with gas.

I spent about a year bouncing around between different proof assistants. There
are several options in this space, each a descendant from a different family of
programming languages. During that year, I came across Agda---a language firmly
in the functional programming camp, with a type-system so powerful that several
years later, I have still only scratched the surface of what's possible. Better
yet, Agda comes with a massive standard library of mathematics. Once you can
wrap your head around Agda programming (no small task), there is a delectable
buffet of ideas waiting to be feasted upon.

Learning Agda has been slow going, and I chipped away at it for a year in the
context of trying to prove things not about mathematics, but about my own
programs. It's nice, for example, to prove your algorithm always gets the right
answer, and to not need to rely on a bevy of tests that hopefully cover the
input space (but how would you ever know if you'd missed a case?).

In the meantime, I had also been experimenting with formalizing my category
theory notes in Agda. That is, I picked up a new textbook, and this time, coded
up all of the definitions and theorems in Agda. Better, I wrote my answers to
the book's exercises as *programs*, and Agda's compiler would yell at me if
there was a flaw in my reasoning. WOW! What a difference this made! All of a
sudden I had the feedback mechanism for mathematics that I'd always wanted. I
could get the red underlines on unconvincing (or wrong) parts of my argument
automatically---all on the order of seconds!

Truly this is a marvelous technology.

When feedback becomes instant, tedious chores turn into games. I found myself
learning mathematics into the late evenings on weekends. I found myself redoing
theorems I'd already proved, trying to find ways of making them prettier, or
more elegant, or more concise, or what have you. I've made more progress in
category theory in the last six months than I had in a decade. I feel now that
proof assistants are the best video game ever invented.

The idea to write this book came a few months later, when some friends of mine
wanted to generalize some well-established applied mathematics and see what
happened. I didn't know anything about the domain, but thought it might be
fun to tag along. Despite not knowing anything, my experience with proving
things in Agda meant I was able to help more than any of us expected.

I came away with the insight that there are a lot more people out there like me:
people who want to be better at mathematics but don't quite know how to get
there. People who are technically minded and have keen domain knowledge, but are
lacking the *proof* side of things. And after all, what is mathematics without
proof?

So we come now to this book. This book is the textbook I ended up writing---not
to teach myself category theory as originally intended, but instead to teach
myself mathematics at large. In the process of explaining the techniques, and
the necessity of linearizing the narrative, I've been forced to grapple with my
understanding of math, and it has become very clear in the places I was fooling
myself. This book is itself a series of Agda modules, meaning it is a fully
type-checked library. That is, it comes with the guarantee that I have told no
lies; at least, none mathematically. I am not an expert in this field, but have
stumbled across a fantastic method of learning and teaching mathematics.

This textbook is the book I wish I had found ten years ago. It would have saved
me a great deal of wasted effort and false starts. I hope it can save you from
the same. Good luck, godspeed, and welcome aboard.

