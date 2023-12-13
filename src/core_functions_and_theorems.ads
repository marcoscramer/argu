with Types; use Types;
with Aux; use Aux;
with Core_Definitions; use Core_Definitions;
with Lemmas;

package Core_Functions_And_Theorems with
   Spark_Mode
is


   function Find_Grounded (F : AF) return ArgSet with
     Post => Is_ArgSet(Find_Grounded'Result,F.Size) and then
             Grounded(Find_Grounded'Result,F) and then
             (for all I in Arbitrary_ArgSets(F.Size)'Range =>
                (if Complete(Arbitrary_ArgSets(F.Size)(I),F) then Subset(Find_Grounded'Result,Arbitrary_ArgSets(F.Size)(I))));

   procedure Exists_Unique_Grounded (F : AF) with
     Ghost,
     Post => (for some I in Arbitrary_ArgSets(F.Size)'Range =>
                (Grounded(Arbitrary_ArgSets(F.Size)(I),F) and
                     not (for some J in Arbitrary_ArgSets(F.Size)'Range =>
                       (Arbitrary_ArgSets(F.Size)(J) /= Arbitrary_ArgSets(F.Size)(I) and
                          Grounded(Arbitrary_ArgSets(F.Size)(J),F)))));

   procedure Exists_Preferred (F : AF) with
     Ghost,
     Post => (for some I in Arbitrary_ArgSets(F.Size)'Range => (Preferred(Arbitrary_ArgSets(F.Size)(I),F)));


   -- Ideas for finding preferred extensions relatively efficiently:
   -- Extend the gunshot algorithm for grounded semantics as follows:
   --  - When Search_Acceptable_Arg returns False, search for minimal ways to extend the current ArgSet while conserving admissibility.
   --  - For this we need a constructive way to loop through sets. -- RETHINK about how this can be done!
   --  - For each possibility that is found, continue in loop.
   --  - When the ArgSet cannot be extended in this way, this shows that it is preferred, so it can be added to the list of preferred extensions, if it's not already in there and if there is still space left in the list.
   --  - We collect the found preferred extensions in a Positive-indexed array going from 1 to Positive'Last.
   --  - The return type is a record that also contains a number N for the number of extensions found. Beyond N, we just fill the list with empty sets. For this we initialize the list to the list of empty sets. N=0 means that more than Positive'Last extensions were found.
   --
   -- Postconditions:
   --  - When N is between 1 and Positive'Last, then the array restricted to the first N elements contains precisely all preferred extensions.
   --  - When N=0, then the array contains only preferred extensions.

end Core_Functions_And_Theorems;
