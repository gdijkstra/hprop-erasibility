module index where

-- Library stuff

import Levels
import Naturals
import Product
import Sigma
import Unit
import Empty

-- Chapter 2: Homotopy type theory

import Identity
-- Definition of identity types along with proofs of several of its
-- properties and definitions of functions such as "transport".

import UIP
-- Proof of UIP using dependent pattern matching (which can also be
-- read as a proof of UIP using J and K). Proof of K using UIP.

import Truncation
-- Definition of truncation levels.

import Proposition
-- Definition of hProp using truncation levels. Proof that this is
-- coinhabited with the definition using proof irrelevance.

import Circle
-- Definition of the circle as a HIT.

import Interval
-- Definition of the interval as a HIT.

import IntervalFunctionExtensionality
-- Proof of function extensionality using the interval type.

import IntervalFunctions
-- Examples of functions on the interval that are definitionally
-- dissimilar, but propositionally equal to eachother.

import FreeSemigroup
-- Definition of a free semigroup as a HIT.

import Univalence
-- Definition of equivalence and the univalence axiom, along with the
-- computation rule.

import Monoid
-- Example of the use of univalence to transport stuff along
-- isomorphisms.

-- Chapter 3: Applications of homotopy type theory

import QuotientUntruncated
-- Construction of quotient types via HITs.

import QuotientBinaryRec
-- Recursion principle for binary operations on quotients.

import Views
-- The JoinList example of non-isomorphic views as seen in the thesis.

import RetractIso
-- Proof of the fact that if we have a retract r : A → B, then B is
-- isomorphic to A/~ with x ~ y defined as r x ≡ r y. We prove it for
-- both the construction using quotients via HITs as the Σ-type
-- construction.

-- Chapter 4: Erasing propositions

import Elem
-- The "elem" example from the thesis.

import Log
-- Example of a Bove-Capretta predicate that admits proof irrelevance.

import Quicksort
-- Attempt at proving that the Bove-Capretta predicate for "qs" admits
-- proof irrelevance.


import PredicatesOnNaturals
-- Examples of collapsible families that are also internally
-- collapsible.

import Irrelevance
-- Some basic results on the irrelevance mechanism of Agda.

import Proposition
-- Some experiments in creating an irrelevant version out of a
-- function that eliminates hProps. We only have results for
-- contractible types (i.e. inhabited hProps) and their indexed
-- versions, as we cannot "pattern match" on an hProp being either
-- empty or inhabited.
