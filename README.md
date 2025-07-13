For now, just a small experiment in defining a weak type theory (WTT) - that is, a dependent type theory without definitional β/η laws - without setoids or quotients. Instead, we define substitution as a *relation*.

The inductive-inductive syntax is defined in [Syntax](RelSSub/Syntax.agda).
We then go on to show that substitution can be computed recursively in
[Comp<>](RelSSub/Comp<>.agda).
