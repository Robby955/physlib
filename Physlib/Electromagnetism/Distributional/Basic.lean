/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
/-!

# Distributional Electromagnetic Potential

## i. Overview

In electromagnetism, charge and current distributions are often idealised as objects
such as point particles, infinitely thin wires, and charged surfaces. These idealisations
are not compatible with the usual demand that physical quantities be specified by a
well-defined value at each point in space: a point charge, for instance, has no finite
value at its location, and the field it sources diverges there.

One way to deal with this is to smear out the idealised objects themselves, replacing a
point charge by a narrow Gaussian distribution and so on. The approach adopted in this
module abandons the premise that physical quantities are defined by
their pointwise values at all. From the point of view of physics this costs nothing, since
no real measuring device probes a single mathematical point; every device has some finite
spatial extent and some smooth response profile across that extent. The most one can ask of
a physical quantity is that it return a well-defined reading for each such response
profile, and that the assignment satisfy two basic conditions: linearity, expressing that
combining two response profiles into a single device adds the readings, and continuity,
expressing that a small change to the response profile produces only a small change to the
reading. Taking the response profiles to be Schwartz maps — smooth functions which,
together with all their derivatives, decay faster than any polynomial at infinity — yields
the mathematical object that captures this picture: a *tempered distribution*, a
continuous linear map sending each Schwartz map to a number, vector, or similar value.

The simplest tempered distributions are those associated with ordinary smooth functions.
A smooth function `f` defines the distribution `φ ↦ ∫ f x * φ x dx`, the weighted average
of `f` against the response profile `φ`. This rule is no longer indexed by the pointwise
values of `f`, but it does not throw any of them away: the function `f` can be recovered
from the distribution it defines. More generally, although a tempered distribution is not
*defined* by its values at points, it may still *have* well-defined values at points, and
those values are extractable when they exist. The distributional point of view does not
erase pointwise information where it is available; it simply refuses to demand it where
it is not.

The electric field of a point charge illustrates both sides of this. The charge itself is
the Dirac delta `q δ(x - x₀)`, the tempered distribution sending each test function `φ` to
`q · φ(x₀)`: physically, the reading of a device with profile `φ` placed near the charge
is `q` weighted by the value of the profile at the location of the charge, exactly as
intuition suggests. The field it sources is the tempered distribution
`Eᵈ : φ ↦ ∫ E x · φ x dx`, where `E` is the Coulomb field
`E(x) = q (x - x₀) / (4π ε₀ |x - x₀|³)`. Away from `x₀` this field is smooth and has a
perfectly well-defined value at every point, and the distribution `Eᵈ` agrees with it
there; only at the location of the charge, where `E` diverges, is no pointwise value
available. The distributional formulation is precisely what allows the global object to be
defined in spite of this single bad point.

Derivatives also continue to make sense in this framework, but they are defined by
integration by parts. For a tempered distribution `f`, the derivative `∂f` is the
distribution acting on test functions by `(∂f) φ := - f (∂φ)`. When `f` is smooth this
reproduces the ordinary derivative — the boundary terms in the integration by parts vanish
because Schwartz functions decay rapidly — but it also assigns a meaningful derivative to
objects such as the step function, whose distributional derivative is the Dirac delta.
This is what allows Maxwell's equations to retain their differential form even when the
sources are singular.

Not every classical construction survives the move to distributions, however.
This is because in general, one does not have access to the pointwise values of the distributions,
and many classical constructions rely on these.
 he Lagrangian density `ℒ = - Aᵤ Jᵘ - ¼ Fᵤᵥ Fᵘᵛ` is a notable casualty: it relies on
pointwise products of distributions (`A` with `J`, and `F` with itself), and in general
the product of two distributions is not defined. For a point charge, for instance, both
`A` and `J` are singular at the location of the charge, and their product has no
distributional meaning.

Other classical constructions need only to be reformulated. Consider the flux of `E` out
of a surface `S`, classically `∫_S E · dA`. The natural distributional analogue is the
flux *weighted by a test function* `φ`, notionally `- ∫ E x · ∇ φ x dx`. Here `φ` plays
the role of a smoothed-out version of the region `V` enclosed by `S`.

This does not mean the classical flux is lost. In the same way that a tempered
distribution may have well-defined values at points without being defined by them, it may
have a well-defined flux through a surface. Whenever
`E` is regular enough on `S` for `∫_S E · dA` to make sense — for instance when `S`
avoids any singularities of `E`, as for any sphere not centred on a point charge — the
weighted fluxes converge to this classical value as `φ` is sharpened, and the two notions
agree. The weighted formulation is what allows the flux to be discussed generally,
including in cases where the surface meets a singularity and the classical integral is
not directly available.

In this setting Gauss's law takes a particularly clean form: the weighted flux equals the
charge measured with the same weighting, up to a factor of `1/ε₀`. Notionally,
`- ∫ E x · ∇ φ x dx = ∫ ρ x φ x dx / ε₀`. Because distributional derivatives are defined
by integration by parts, this 'integral' form is exactly equivalent to the differential
form `∇ · E = ρ / ε₀`, with no separate passage between the two.

For points `x` where both `ρ` is defined, this distributional Gauss's law
implies that `∇ · E x = ρ x / ε₀`, as one would expect.

-/
