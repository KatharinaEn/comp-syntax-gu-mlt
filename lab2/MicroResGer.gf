resource MicroResGer = {

    param
      Number = Sg | Pl ;
      Case = Nom | Gen | Dat | Acc ;
      Gender = Masc | Fem | Neut ;
      Person = P1 | P2 | P3 ; 
      Declension = Strong | Weak | Mixed | Pred ;
      NumberGender = SgAdj Gender | PlAdj ; 
      VForm = Inf | VPresT Person Number ;
--      NPAgreement = Number | Person | Gender | Case ; 
      Aux = haben | sein ;

  
    oper
      Noun : Type = {s : Number => Case => Str ; g : Gender} ;

      mkNoun : (sgnom, sggen, sgdat, sgacc, plnom, plgen, pldat, placc : Str) -> Gender -> Noun
         = \sgnom, sggen, sgdat, sgacc, plnom, plgen, pldat, placc, g -> {
          s = table {
             Sg => table {
                    Nom => sgnom ;
                    Gen => sggen ;
                    Dat => sgdat ;
                    Acc => sgacc 
                } ;
                Pl => table {
                    Nom => plnom ;
                    Gen => plgen ;
                    Dat => pldat ;
                    Acc => placc 
                }
              } ;
              g = g;
                } ;

 
    smartNoun : Str -> Gender -> Noun = \sg,g -> case sg of {
      x + ("p" |"b" |"m" |"n" |"f" |"v" |"t" |"s" |"d" |"z" |"l" |"sch" |"ch" |"j" |"k" |"g" |"r" |"l") => mkNoun sg (sg +"s") sg sg (sg + "ä" + "e") (sg + "ä" + "e") (sg + "ä" + "en") (sg + "ä" + "e") g ; 
      x + ("n" | "en" | "e") => mkNoun sg (sg + "en") (sg+"en") (sg+"en")(sg+"en") (sg+"en")(sg+"en")(sg+"en") g ; 
      x + ("s") => mkNoun sg (sg + "s") sg sg (sg+ "s") (sg +"s") (sg +"s") (sg +"s") g ;
      _ => mkNoun sg (sg +"s") sg sg sg sg (sg + "n") sg g                 
    } ;

    irregNoun : Str -> Str -> Gender -> Noun = \sg,pl,g ->
      let sgnom : Str = sg ; 
          sggen : Str = (sgnom + "es") ;
          sgdat : Str = sgnom ;
          sgacc : Str = sgnom ;
          plnom : Str = pl ; 
          plgen : Str = pl ;
          pldat : Str = (pl + "n") ;
          placc : Str = pl ;
      in mkNoun sg sggen sgdat sgacc pl plgen pldat placc g  ;



 
 -- I'll focus only on pos (positive) for all forms: strong, weak, and mixed
-- I only focused on singular and plural as well as weak,strong,and mixed for the postive. I don't do the prad (Prädikativ).

oper

  Adjective : Type = {s : Declension => NumberGender => Case => Str} ;
  mkAdjective : Str -> Adjective = \pos -> {
    s = table {
        Strong => table {
            SgAdj Masc => table {
                            Nom => pos + "er" ;
                            Gen => pos + "en" ;
                            Dat => pos + "em" ;
                            Acc => pos + "en" 
                        } ;
            SgAdj Fem => table {
                            Nom => pos + "e" ;
                            Gen => pos + "er" ;
                            Dat => pos + "er" ;
                            Acc => pos + "e"
                        } ;
            SgAdj Neut => table {
                            Nom => pos + "es" ;
                            Gen => pos + "en" ;
                            Dat => pos + "em" ;
                            Acc => pos + "es"
                        } ;
            PlAdj => table {
                            Nom => pos + "e" ;
                            Gen => pos + "er" ;
                            Dat => pos + "en" ;
                            Acc =>  pos + "e"
                            }
        } ; -- this ends the strong table
        Weak => table {
            SgAdj Masc => table {
                            Nom => pos + "e" ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc =>  pos + "en"
                        } ;
            SgAdj Fem => table {
                            Nom => pos + "e" ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc =>  pos + "e"
                        } ;
            SgAdj Neut => table {
                            Nom => pos + "e"  ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc => pos + "e"
                        } ;
            PlAdj => table {
                            Nom => pos + "en"  ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc => pos + "en"
                    }
        } ; -- this ends the weak table
        Mixed => table {
            SgAdj Masc => table {
                            Nom => pos + "er" ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc => pos + "en"
                        } ;
            SgAdj Fem => table {
                            Nom => pos + "e" ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc => pos + "e"
                        } ;
            SgAdj Neut => table {
                            Nom => pos + "es" ;
                            Gen => pos + "en" ;
                            Dat => pos + "en" ;
                            Acc => pos + "es"
                        } ;
            PlAdj => table {
                        Nom => pos + "en"  ;
                        Gen => pos + "en" ;
                        Dat => pos + "en" ;
                        Acc => pos + "en"
            }
    } ;   -- this ends the mixed table
    Pred => table {cas => table {gennum => pos}} -- gennum = Gender + Number
  }  -- here ends the full s
} ; -- this ends the whole Adjective record



  
-- For the verbs only the present tense is going to be considered 

oper
Verb : Type = {s : VForm => Str} ;

   mkVerb : (inf,stem,sg1,sg2,sg3,pl1,pl2,pl3 : Str) -> Verb
    = \inf,stem,sg1,sg2,sg3,pl1,pl2,pl3  -> {
    s = table {
      Inf => inf ;
      VPresT P1 Sg => sg1;
      VPresT P2 Sg => sg2;
      VPresT P3 Sg => sg3;
      VPresT P1 Pl => pl1;
      VPresT P2 Pl => pl2;
      VPresT P3 Pl => pl3
       }
    } ;

-- kaufen, warten, reden, ... schwache Verben "buying, waiting, talking, ..." reguläre Verben 
mkVerb1 : (inf, stem : Str) -> Verb 
    =\ inf, stem -> {
    s = table {
      Inf => inf ;
      VPresT P1 Sg => (stem + "e") ; -- ich kaufe 
      VPresT P2 Sg => (stem + "st") ; -- du kaufst
      VPresT P3 Sg => (stem + "t") ; -- er/sie/es kauft
      VPresT P1 Pl => (stem + "en") ; -- sie kaufen 
      VPresT P2 Pl => (stem + "t") ; -- Sie/Er kauft
      VPresT P3 Pl => (stem + "en")  -- sie kaufen 
      }
    } ; 

-- fahren, schlafen, ... starke Verben "driving, sleeping, ..."  11 = 1.1 irreguläre Verben 
mkVerb11 : (inf, stem : Str) -> Verb 
  =\ inf, stem -> {
    s = table {
      Inf => inf ;
      VPresT P1 Sg => (stem + "e") ; -- ich schlafe 
      VPresT P2 Sg => (stem + "ä" + "st") ; -- du schäfst
      VPresT P3 Sg => (stem + "ä" + "t") ;  -- er/sie/es schläft
      VPresT P1 Pl => (stem + "en") ; -- wir schlafen
      VPresT P2 Pl => (stem + "ä" + "t") ; -- Sie/Er schläft 
      VPresT P3 Pl => (stem + "en") -- sie schlafen 
      }
    } ; 

-- sich waschen - V2 "wash" 
mkVerb2 : (inf, stem : Str) -> Verb 
  =\ inf, stem -> {
    s = table {
      Inf => inf ;
      VPresT P1 Sg => (stem + "e") ; -- ich wasche mich
      VPresT P2 Sg => (stem + "ä" + "st") ; -- du wäschst dich
      VPresT P3 Sg => (stem + "ä" + "t") ;  -- er/sie/es wäscht sich 
      VPresT P1 Pl => (stem + "en") ; -- sie waschen sich
      VPresT P2 Pl => (stem + "ä" + "t") ; -- Sie/Er wäscht sich
      VPresT P3 Pl => (stem + "en") -- sie waschen sich 
      }
  } ; 

  smartVerb : Str -> Verb = \stem -> case stem of {
    kauf + "en" => mkVerb1 stem kauf ;     -- kaufen ; schwache Verben
    fahr + "en" => mkVerb11 stem fahr ;     -- fahren ; starke Verben irreguläre Verben 
    wasch + "en" => mkVerb2 stem wasch  -- reflexive Verben V2 sich waschen 
    } ;


  irregVerb : (inf,stem,sg1,sg2,sg3,pl1,pl2,pl3 : Str) -> Verb =
    \stem,sg1,sg2,sg3,pl1,pl2,pl3 ->
      let verb = smartVerb stem 
	      in mkVerb stem sg1 sg2 sg3 pl1 pl2 pl3 ;

  Verb2 : Type = Verb ** {c : Str} ; 

  be_Verb : Verb = mkVerb "sein" "bin" "bist" "ist" "sind" "seid" "sind" "-" ; 

  Preposition : Type = {s : Str; c : Case} ;
} ; 