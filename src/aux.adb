package body Aux with
   Spark_Mode
is


   function ArgSet_From_ArgList (L : ArgList; N : AFSize) return ArgSet is
      S : ArgSet := (1 .. MaxNumberOfArgs => False);
   begin

      for K in 1 .. L.Size loop
         pragma Loop_Invariant (for all I in 1 .. N => (if S(I) then (for some J in 1 .. K-1 => L.List(J) = I)));
         pragma Loop_Invariant (for all I in 1 .. N => (if (for some J in 1 .. K-1 => L.List(J) = I) then S(I)));
         pragma Loop_Invariant (for all I in N+1 .. MaxNumberOfArgs => not S(I));
         S(L.List(K)) := True;
      end loop;
      return S;

   end ArgSet_From_ArgList;


   function Arbitrary_ArgSets (N : AFSize) return ArgSetArray is
      S : ArgSet := (1 .. MaxNumberOfArgs => False);
      R : ArgSetArray := (1 .. 1 => S);
   begin

      return R;

   end Arbitrary_ArgSets;


   function Exists_ArgSet_Intro (N : AFSize; S : ArgSet) return Positive is
      I : Positive := Arbitrary_ArgSets(N)'First;
   begin

      -- This function together with Arbitrary_ArgSets ensures that we can quantify over ArgSets and reason meaningfully with such quantifiers.
      -- The following pragma Assume is needed in order to conclude an existentially quantified statement from a specific instance of an ArgSet with the required property.
      pragma Assume (S = Arbitrary_ArgSets(N)(I));

      return I;

   end Exists_ArgSet_Intro;


end Aux;
