# Double-copy-structure-From-QCD-to-gravity
This is my master's thesis. In here, I reproduce the result from a known article, "Graviton emission in EH gravity", with new libraries that allow the computations of QG  diagrams more straightforwardly.
Later on, my master's thesis will be uploaded. In there, I have made a brief introduction to the double copy structure, starting from the BCJ duality in QFT, until the KLT relations in string theory. I also introduce the concept of supersymmetries, which has interest in this field. Furthermore, I introduce perturbative quantum gravity as well as the high-energy limit, with its resummation process and some useful approximations.

The two codes currently uploaded are what I have used in the procedure.

The code called "QQ-QQG" (which represents a process involving two different quarks combining into two quarks and a gluon) calculates an effective vertex in the high-energy (or Regge) limit. This effective vertex consists on 3 gluons, 2 of which are off-shell, while the other is on-shell. Let me call this vertex $\Omega^\mu$

The code, called "SS-SSG" (representing a process involving two different scalars that combine into two scalars and a graviton), works with quantum gravity and yields an effective vertex with three gravitons, two of which are off-shell, while the other is on-shell. Let me call this vertex $\Omega^{\mu \nu}$.

In my master's thesis, a link between these two vertices is given, with the so-called double copy structure. The naive approach would be $\Omega^{\mu \nu} = \Omega^{\mu}\Omega^{\nu}$. This does not follow the so-called Steinmann rules. We reproduce the solution proposed before, which is $\Omega^{\mu \nu} = \Omega^{\mu}\Omega^{\nu} - \mathcal{N}^\mu \mathcal{N}^\nu$. This does follow the Steinmann rules. More details can be found in the thesis.

Finally, in the master's thesis, I talk about the application that this may have in the computations of higher-order loops, as well as the different ways that this can be upgraded.
