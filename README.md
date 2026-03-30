## Some experiments in mechanised metatheory of type theory

### Finished:

- A definition of a weak type theory (WTT) - that is, a dependent type theory without definitional β/η laws - without setoids or quotients. Instead, we define (single) substitution as a *relation*.
  - The inductive-inductive syntax is defined in [Syntax](WTT/Syntax.agda).
  - We then go on to show that substitution can be computed recursively in [Comp<>](WTT/Comp<>.agda).
  - We also construct the standard model in [Model](WTT/Model.agda).
  - I think the especially interesting aspect here is that, because there is no redundancy in the substitution relation, the syntax should still be coherent `--without-K` and interpreting this syntax into arbitry n-types (rather than just hSets) should be possible, though I have not yet gone through the details `--without-K` to check this actually works.

### WIP:

- The groupoid model: [GrpdModel](Models/GrpdModel.agda)
  - I mostly just wanted to understand the computational content of `J` in the groupoid model. I believe finishing the rest of the mechanisation would be extremely painful.
- NbE (including trying out an idea I have to deal with non-linear reductions): [NonLinNbE](NonLinNbE/NbE.agda)
  - This is still very-much WIP. I will write more here after I make more progress.
  - I have now posted a small summary of the idea on Mastodon though: https://types.pl/deck/@NathanielB/116256378457107811
