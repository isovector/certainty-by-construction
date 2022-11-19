# Expectations

This book is aimed at a (comparatively) wide audience; targeting people who know
little math and little functional programming, as well as veteran functional
programmers who want to brush up on their mathematics. As a result, the
difficulty curve in this book necessarily must have a bit of a J shape. We need
to start slowly in order to get everyone on the same page, but once we get
going, we will move quickly.

The introductory material has several goals; one: to motivate Agda, and gain
enough of a passing familiarity with it to get real work done. Two: to learn
enough about Agda's type system to be able to quickly formalize whatever it is
we're trying to say. Three: to motivate the technique of *writing proofs* in a
domain we're familiar with; that is, simple algebra problems and theorems about
data structures. Four: motivate mathematics, and demonstrate that pure
mathematics is not nearly as far away from programming as it might seem. Five:
illustrate that learning mathematics is both fun for its own sake, as well as
valuable for it's ability to help us think clearly about matters of programming.

That's certainly our work cut out for us, just in the introductory material,
before we even get to the more interesting mathematics! What you should expect
is thus about one third of the material to be getting up to speed, one third
about mathematics for its own sake, and one third to be reapplying our new
machinery to problems of computer science. If you are already familiar with
functional programming, or know what makes for a convincing proof, feel free to
skim or even skip the first third of this book. Should you come across something
you don't understand later on, that would be a good time to come back and find
the missing knowledge.

However, if you're a beginner, do start from the beginning and work your way
through the introductory material. It's been carefully organized to get you up
to speed as quickly as possible, introducing concepts in the right order and
building on itself. Interleaved into every chapter are exercises, which the
motivated student would be wise to do. The exercises are never onerous once you
understand the concepts. Thus, if you understand the material, the exercises
will be quick and help to cement the ideas. And if you don't, in fact,
understand the material, the exercises will be immediate feedback that something
has gone amiss.

Something notable about this book is that it is a living code document. Every
chapter has inline code snippets of Agda, and the source material of the *prose*
is interleaved with the code. That is to say, all of the code examples are
*complete* and *verified to be corrected.* Unfortunately, the same cannot be
said of the prose, but that is a necessary risk whenever dealing with informal
languages like the natural ones we speak.

A corollary of every chapter being a module of code is that chapters can
literally build on one another. If we introduce a concept in chapter 3, we can
*import* those definitions in chapter 4 to continue building. If you were to
follow along with every exercise and definition in your own codebase, the
resulting artifact would be a software library of all the mathematics you have
formalized up to that point. I have personally found this to be extremely
valuable; not only does coding up the material require me to truly understand
it, it leaves behind an artifact that I can reference in the future should I
forget the exact details. In fact, I have found myself referencing my old
codebases in which I formalized other textbooks I was working through in the
production of this text.

Having a strict, automatic, fast-feedback tool is the primary benefit of working
in a proof-assistant. It prevents us from fooling ourselves that we understand
what we're talking about. But a very close second benefit is reifying all of our
knowledge into a tractable artifact that can persist much longer than our human
memories can. This is a gift; do use it.

