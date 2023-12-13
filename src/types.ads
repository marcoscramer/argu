package Types with
   Spark_Mode
is


   MaxNumberOfArgs : constant Integer := 1000;

   subtype Arg is Positive range 1 .. MaxNumberOfArgs;

   subtype AFSize is Natural range 0 .. MaxNumberOfArgs;

   type BoolMatrix is array (Arg, Arg) of Boolean;

   type AF is record
      Size : Natural;
      AdjacencyMatrix : BoolMatrix;
   end record with
     Dynamic_Predicate => AF.Size <= MaxNumberOfArgs and then
      (for all I in 1 .. MaxNumberOfArgs => (for all J in 1 .. MaxNumberOfArgs =>
           (if I > AF.Size or J > AF.Size then not AF.AdjacencyMatrix(I,J))));

   type ArgPair is array (Positive range 1 .. 2) of Arg;

   type AF_Graph is array (Positive range <>) of ArgPair;

   type ArgSet is array (Positive range 1 .. MaxNumberOfArgs) of Boolean;

   type NatArray is array (Positive range 1 .. MaxNumberOfArgs) of Natural;

   type ArgList is record
      Size : Natural;
      List : NatArray;
   end record with
     Dynamic_Predicate => ArgList.Size <= MaxNumberOfArgs and then
        (for all I in 1 .. ArgList.Size => (ArgList.List(I) /= 0 and
           not (for some J in 1 .. ArgList.Size => (J /= I and ArgList.List(J) = ArgList.List(I))))) and then
        (for all I in ArgList.Size+1 .. MaxNumberOfArgs => ArgList.List(I) = 0);

   type InputArgList is array (Positive range <>) of Arg;

   type ArgSetArray is array (Positive range <>) of ArgSet;

   type SearchResult (Exists : Boolean := False) is record
      case Exists is
         when True =>
            Arg : Positive;
         when False =>
            null;
      end case;
   end record;

   type CheckReturnType (Valid_Input : Boolean := False) is record
      case Valid_Input is
         when True =>
            Output : Boolean;
         when False =>
            null;
      end case;
   end record;

   end Types;
