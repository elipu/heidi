import Logickit

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Abstract Syntax §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Abstract syntax: From Heidi ===========================
/*
  Commands = {davent,davos,deponer,dretg,plaun,returnar,sanester, saFermar}  (in Romansh)

   __________________
    comm ϵ Commands


     comm ϵ Commands , c ϵ List
   -------------------------------   (Sequence of Commands)
         comm :: c ϵ List

*/
// Commands:
let davent = value("davent")
let davos = value("davos")
let deponer = value("deponer")
let dretg = value("dretg")
let plaun = value("plaun")
let returnar = value("returnar")
let sanester =value("sanester")
let saFermar = value("sa fermar")
// ====================== Abstract syntax: From Tita ===========================
/*
  Whistles = {short,long,pause,hee,who,wheeo,whee,wheet}

   __________________
    whist ϵ Whistles


       whist ϵ Whistles\{pause} , w ϵ List
   -------------------------------------------   (Sequence of whistles = whistle command)
         whist :: w ϵ WhistleCommand

        whist ϵ WhistleCommand , p = pause , w ϵ WhistleCommand
   --------------------------------------------------------------    (Sequence of whistle commands = work session)
                  whist :: p :: w ϵ  WorkSession

    (pause is to distinguish between whistle commands)

*/
// Whistles:
let short = value("short")
let long = value("long")
let pause = value("pause")         // a pause is just a silent whistle ¯\_(ツ)_/¯
let hee = value("hee")
let who = value("who")
let wheeo = value("wheeo")
let whee = value("whee")
let wheet = value("wheet")

// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Semantics §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Semantics: Heidi to Tita ===========================
/*

    davent ϵ Commands , wheet::wheeo::wheet::wheet ϵ WhistleCommand
   ------------------------------------------------------------------
            davent ---HtoT---> wheet::wheeo::wheet::wheet


     davos ϵ Commands , who::hee::who ϵ WhistleCommand
    ----------------------------------------------------
            davos ---HtoT---> who::hee:who

      deponer ϵ Commands , short::short ϵ WhistleCommand
     -----------------------------------------------------
             deponer ---HtoT---> short::short

       dretg ϵ Commands , whee::who ϵ WhistleCommand
      ---------------------------------------------------
              dretg ---HtoT---> whee:who

      plaun ϵ Commands , hee::hee::hee::hee ϵ WhistleCommand
     ---------------------------------------------------------
             plaun ---HtoT---> hee::hee::hee::hee

       returnar ϵ Commands , whee::whee::wheet ϵ WhistleCommand
     -----------------------------------------------------------
              returnar ---HtoT---> whee::whee::wheet

      sanester ϵ Commands , whee:t:wheeo ϵ WhistleCommand
     -----------------------------------------------------
             sanester ---HtoT---> wheet::wheeo

     saFermar ϵ Commands , long ϵ WhistleCommand
    -------------------------------------------------
              saFermar ---HtoT---> long
*/

func HT_Davent(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === davos
            &&
         Whistle === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.cons(pause, [])))))
}

func HT_Davos(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === davos
            &&
         Whistle === List.cons(who, List.cons(hee, List.cons(who, List.cons(pause, []))))
}

func HT_Deponer(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === deponer
            &&
         Whistle === List.cons(short, List.cons(short, List.cons(pause, [])))
}

func HT_Dretg(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === dretg
            &&
         Whistle === List.cons(whee, List.cons(who, List.cons(pause, [])))
}

func HT_Plaun(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === plaun
            &&
         Whistle === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.cons(pause, [])))))
}

func HT_Returnar(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === returnar
            &&
         Whistle === List.cons(whee, List.cons(whee, List.cons(wheet, List.cons(pause, []))))
}

func HT_Sanester(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === sanester
            &&
         Whistle === List.cons(wheet, List.cons(wheeo, List.cons(pause, [])))
}

func HT_SaFermar(_ Command_input: Term, _ Whistle_output: Term) -> Goal {

  return Command === saFermar
            &&
         Whistle === List.cons(long, List.cons(pause, []))
}

// ===================== Semantics: Tita to Heidi ===========================
/*

    wheet::wheeo::wheet::wheet ϵ WhistleCommand , davent ϵ Commands
   ------------------------------------------------------------------
            wheet::wheeo::wheet::wheet ---TtoH---> davent


     who::hee::who ϵ WhistleCommand , davos ϵ Commands
    ----------------------------------------------------
            who::hee:who ---TtoH---> davos

      short::short ϵ WhistleCommand , deponer ϵ Commands
     -----------------------------------------------------
            short::short ---TtoH---> deponer

        whee::who ϵ WhistleCommand , dretg ϵ Commands
      ---------------------------------------------------
              whee:who ---TtoH---> dretg

       hee::hee::hee::hee ϵ WhistleCommand , plaun ϵ Commands
     ----------------------------------------------------------
             hee::hee::hee::hee ---TtoH---> plaun

       whee::whee::wheet ϵ WhistleCommand , returnar ϵ Commands
      ----------------------------------------------------------
              whee::whee::wheet ---TtoH---> returnar

      whee:t:wheeo ϵ WhistleCommand , sanester ϵ Commands
     -----------------------------------------------------
            wheet::wheeo  ---TtoH---> sanester

      long ϵ WhistleCommand , saFermar ϵ Commands
    -------------------------------------------------
              long ---TtoH---> saFermar
*/

// =========================== Translator =====================================

// func Translate_HT(_ Command: Term, _ Translation: Term){
//
//   return (Command === List.empty && Translation === List.empty) ||
//
//          freshn { l in let ch = l["ch"]
//                        let ct = l["ct"]
//                        let tt = l["tt"]
//
//                  (Command === List.cons(ch,ct)) &&
//                  (
//                    ch === davent && HT_Davent(ch,tt) ||
//                    ch === davos && HT_Davos(ch,tt) ||
//                    ch ===
//                  )}
// }









// ##########################################################################################################
// ##########################################################################################################
// ############################################## Optimisation ##############################################
// ##########################################################################################################
// ##########################################################################################################

// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Abstract Syntax §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// Same abstract syntaxes, except for the set Whistles:
// Whistles = {hee,wheet,wheeo,pause}


// ==========================================================================================================
// §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§ Semantics §§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§§

// ===================== Semantics: Heidi to Tita ===========================
/*

    davent ϵ Commands , wheet::hee::wheet ϵ WhistleCommand
   ------------------------------------------------------------------
            davent ---HtoT---> wheet::hee::wheet


     davos ϵ Commands , wheet::wheeo:wheet ϵ WhistleCommand
    ----------------------------------------------------
            davos ---HtoT---> wheet::wheeo:wheet

      deponer ϵ Commands , wheeo::hee::wheet ϵ WhistleCommand
     -----------------------------------------------------
             deponer ---HtoT---> wheeo::hee::wheet

       dretg ϵ Commands , hee::wheet ϵ WhistleCommand
      ---------------------------------------------------
              dretg ---HtoT---> hee::wheet

      plaun ϵ Commands , wheet::wheeo::wheeo ϵ WhistleCommand
     ---------------------------------------------------------
             plaun ---HtoT---> wheet::wheeo::wheeo

       returnar ϵ Commands , wheeo::wheet ϵ WhistleCommand
      ----------------------------------------------------------
              returnar ---HtoT---> wheeo::wheet

      sanester ϵ Commands , wheet::wheeo ϵ WhistleCommand
     -----------------------------------------------------
             sanester ---HtoT---> wheet::wheeo

     saFermar ϵ Commands , wheeo::wheeo ϵ WhistleCommand
    -------------------------------------------------
              saFermar ---HtoT---> wheeo::wheeo
*/







// ===================== Semantics: Tita to Heidi ===========================
/*

    wheet::hee::wheet ϵ WhistleCommand , davent ϵ Commands
   ---------------------------------------------------------
            wheet::hee::wheet ---TtoH---> davent


     wheet::wheeo:wheet ϵ WhistleCommand , davos ϵ Commands
    ---------------------------------------------------------
            wheet::wheeo:wheet ---TtoH---> davos

      wheeo::hee::wheet ϵ WhistleCommand , deponer ϵ Commands
     ---------------------------------------------------------
            wheeo::hee::wheet ---TtoH---> deponer

        hee::wheet ϵ WhistleCommand , dretg ϵ Commands
      ---------------------------------------------------
              hee::wheet ---TtoH---> dretg

       wheet::wheeo::wheeo ϵ WhistleCommand , plaun ϵ Commands
     -----------------------------------------------------------
             wheet::wheeo::wheeo ---TtoH---> plaun

       wheeo::wheet ϵ WhistleCommand , returnar ϵ Commands
      -------------------------------------------------------
              wheeo::wheet ---TtoH---> returnar

      wheet::wheeo ϵ WhistleCommand , sanester ϵ Commands
     ------------------------------------------------------
            wheet::wheeo  ---TtoH---> sanester

      wheeo::wheeo ϵ WhistleCommand , saFermar ϵ Commands
    -------------------------------------------------------
              wheeo::wheeo ---TtoH---> saFermar
*/
