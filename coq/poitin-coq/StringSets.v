Require Import FSetList.
Require Import FSetNotin.
Require Import StringOrdered.
Module StringSet := Make(StringOrder).
Module StringSetNotin  := FSetNotin.Notin(StringSet).