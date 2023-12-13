package body Lemmas with
   Spark_Mode
is


   procedure Admissible_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) is
   begin

      pragma Assert (if S1 = S2 and Admissible(S1,F) then Admissible(S2,F));

   end Admissible_by_Equality;


   procedure Defense_by_Equality (S1 : ArgSet; S2 : ArgSet; a: Arg; F : AF) is
   begin

      pragma Assert (if S1 = S2 and Defends(S1,a,F) then Defends(S2,a,F));

   end Defense_by_Equality;


   procedure Complete_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) is
   begin

      Admissible_by_Equality(S1,S2,F);
      for a in 1 .. F.Size loop
         pragma Loop_Invariant (for all I in 1 .. a-1 => (if S2(I) then Defends(S2,I,F)));
         if S2(a) then
            Defense_by_Equality(S1,S2,a,F);
         end if;
      end loop;

   end Complete_by_Equality;


   procedure Grounded_by_Equality (S1 : ArgSet; S2 : ArgSet; F : AF) is
   begin

      Complete_by_Equality(S1,S2,F);
      for I in Arbitrary_ArgSets(F.Size)'Range loop
         pragma Loop_Invariant (for all J in Arbitrary_ArgSets(F.Size)'First .. I-1 =>
                                  ((if Subset(Arbitrary_ArgSets(F.Size)(J),S2) and Complete(Arbitrary_ArgSets(F.Size)(J),F) then
                                       S2 = (Arbitrary_ArgSets(F.Size)(J)))));
         if Subset(Arbitrary_ArgSets(F.Size)(I),S2) and Complete(Arbitrary_ArgSets(F.Size)(I),F) then
            pragma Assert (S2 = (Arbitrary_ArgSets(F.Size)(I)));
         end if;
      end loop;

   end Grounded_by_Equality;


   procedure Every_Complete_Extension_Contains(a : Arg; R : ArgSet; F : AF) is
   begin

      for I in Arbitrary_ArgSets(F.Size)'Range loop
         pragma Loop_Invariant (for all J in Arbitrary_ArgSets(F.Size)'First .. I-1 => (if Complete(Arbitrary_ArgSets(F.Size)(J),F) then Arbitrary_ArgSets(F.Size)(J)(a)));
         if Complete(Arbitrary_ArgSets(F.Size)(I),F) then
            pragma Assert (Defends(Arbitrary_ArgSets(F.Size)(I),a,F));
         end if;
      end loop;

   end Every_Complete_Extension_Contains;


   function Search_Acceptable_Arg (S : ArgSet; F : AF) return SearchResult is
   begin

      for a in 1 .. F.Size loop
         pragma Loop_Invariant (for all b in 1 .. a-1 => (if not S(b) then not Defends(S,b,F)));
         if not S(a) and Defends(S,a,F) then
            return SearchResult'(Exists => True, Arg => a);
         end if;
      end loop;

      return SearchResult'(Exists => False, others => <>);

   end Search_Acceptable_Arg;


   procedure Extend_Admissible_List (L : in out ArgList; a : in Arg; F : in AF) is
      NewList : NatArray := L.List;
      NewL : ArgList;
   begin

      --pragma Assert(Is_ArgList_For(L,F));
      pragma Assert (for some a in 1.. F.Size => not ArgSet_From_ArgList(L,F.Size)(a));
      Counting.ArgList_Not_Full(L,F.Size);
      NewList(L.Size+1) := a;
      NewL := ArgList'(Size => L.Size+1, List => NewList);
      Extend_Admissible(ArgSet_From_ArgList(L,F.Size),ArgSet_From_ArgList(NewL,F.Size),a,F);
      L := NewL;
      --pragma Assert (Conflict_Free(ArgSet_From_ArgList(L,F),F));
      --pragma Assert (Defends(ArgSet_From_ArgList(L,F),a,F));

   end Extend_Admissible_List;


   procedure Extend_Admissible (S1 : in ArgSet; S2 : in ArgSet; a : in Arg; F : in AF) is
   begin

      --S(a) := True;
      pragma Assert (Conflict_Free(S2,F));
      pragma Assert (Defends(S2,a,F));

   end Extend_Admissible;

end Lemmas;
