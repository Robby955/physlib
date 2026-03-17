/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import PhysLean.Meta.Requirements.Basic
/-!

# The Atlas for Electromagnetism

An atlas is a collection of APIs and requirements for a given area of physics.
This is the implementation-independent structure of the area.

-/
@[expose] public section

def API.EMPotential : API where
  name := "Electromagnetic Potential"
  description := "The API associated with the electromagnetic potential."


def Requirement.EMPotential.definition : Requirement where
  name := "The definition of the electromagnetic potential."
  description := "The API shall contain a definition of space of
    electromagnetic potentials."
  api := API.EMPotential

/-- The API shall contain an action of the Lorentz group on
    the electromagnetic potential. -/
def Requirement.EMPotential.groupAction : Requirement where
  name := "Group action on the electromagnetic potential."
  description := "The API shall contain an action of the Lorentz group on
    the electromagnetic potential."
  api := API.EMPotential

def Requirement.EMPotential.magneticField : Requirement where
  name := "Magnetic field from the electromagnetic potential."
  description := "The API shall contain the definition of the magnetic field from the
    electromagnetic potential."
  api := API.EMPotential
