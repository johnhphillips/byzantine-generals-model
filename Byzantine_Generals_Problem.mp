/*-------------------------------------------------------------------------------
Model of the Byzantine Generals Problem  

Created by:
John Phillips in November 2023

Edited by:
John Phillips in November 2023

Purpose:


Description: 

   
Assumptions:
1. The order is attack. 
2. All messages sent are received. 
3. All messages are not tamperable (changed in transit). 
4. Once a traitor, always a traitor. 


Instructions:

Trace Count: 48 traces at Scope 2 
Elapsed time: 1.17 sec

TODOs: 
1. Need to figure out how to make a traitor stay a traitor.  
      


-------------------------------------------------------------------------------*/ 

SCHEMA Byzantine_Generals_Problem

/* Placeholder variables to hold trace information. */
ATTRIBUTES { number a, b, c, d, e; };

ATTRIBUTES { number Generals, General_ID, Round, Rounds, Traitor, Traitors; };

Generals := 3;

Traitors := 1;

Rounds :=  ( Traitors + 1 ) * Generals;

/* Used to track trace versions over time. */
SAY ( "Version 20231113" );

/* Mark each trace with the trace number. */
SAY ( "Trace " trace_id );

ROOT Army: 
	{+ {[General], General} +}

BUILD {
	General_ID := 1;
        
	COORDINATE  $a: General
		DO $a.General_ID := General_ID; General_ID +:= 1; OD;   
}
;

	General:
		(+ 
        	( Attack | Retreat )
            Send_Messages
            Receive_Messages
		+)

	BUILD {
                 
     	/* Set the round value for iteration. */
        Round := 1;
        
        COORDINATE	$a: ( Attack | Retreat ),
        			$b: Send_Messages,
        			$c: Receive_Messages
        	DO $a.Round := Round; 
        	   $b.Round := Round; 
        	   $c.Round := Round; Round +:= 1; OD;

        /* Once a traitor, always a traitor. */
      
        COORDINATE	$a: ( Retreat )
        	DO IF $a.Round == 1 THEN ENSURE #Attack == 0; FI; OD;
        
    }
	;

/* Set the number of Generals. */
ENSURE #General == Generals;

/* Set the number of rounds. */
ENSURE #Send_Messages == Rounds;

/* Check that the first round initial conditions (number of 
   traitors is met. */
COORDINATE	$a: General
	DO COORDINATE $b: ( Attack | Retreat ) FROM $a
		DO IF ( $b.Round == 1 ) THEN
			IF $b IS Retreat THEN $a.Traitor := 1; a := 1; 			
			ELSE a := 0; FI; 			
			b +:= a;
		   FI;
		OD;
	OD;

/* Set the number of Traitors. */
IF b > Traitors THEN REJECT; FI;

/* Remove traces without a Traitor. */
IF b == 0 THEN REJECT; FI;

GRAPH messages { };

WITHIN messages {
	COORDINATE  $a: General
    	DO COORDINATE  $b: ( Attack | Retreat ) FROM $a,
                       $c: Send_Messages FROM $a
    
			DO COORDINATE  $d: General
    			DO COORDINATE $e: Receive_Messages FROM $d
					DO
    	    			IF NOT $b IN $d THEN 
							IF $b IS Attack THEN a := 1; ELSE a := 0; FI;
    						IF ( $c.Round == $e.Round ) THEN 
    	
								ADD $c Message $e;
    
    							IF $c.Round == 1 THEN
									/* What happened. */
    								Node$x: NEW ( $c.Round );    
    								Node$x.a := ( $d.General_ID );
									Node$x.b := ( $a.General_ID );
    								Node$x.c := ( a );
    								Node$x.d := ( 0 );
    								/* What they said happened. */
    								Node$y: NEW ( $c.Round );
    								Node$y.a := ( $d.General_ID );
									Node$y.b := ( $a.General_ID );
    								IF $d.Traitor == 1 THEN
    									Node$y.c := ( 0 );
    								ELSE
    									Node$y.c := ( a );    							
    								FI;
    								Node$y.d := ( 1 );
    							FI;
    						FI;
						FI;
					OD;
    			OD;
			OD;      
    	OD;
}
;

TABLE direct_messages {
	TITLE ("Trace " trace_id " Direct");
	TABS 	string R, 
    		number G,
			number M,
    		number O;
}
;

WITHIN messages {
    FOR Node$n
    	DO
		IF Node$n.d == 0 THEN
    		
			direct_messages <|
				R:		SAY(Node$n), 
    			G:		Node$n.a,
				M: 		Node$n.b,
    			O:		Node$n.c;
		FI;
    	OD;

}
;

TABLE relayed_messages {
	TITLE ("Trace " trace_id " Relayed");
	TABS 	string R, 
    		number G,
			number M,
    		number O;
}
;

WITHIN messages {
    FOR Node$n
    	DO
		IF Node$n.d == 1 THEN
    		
			relayed_messages <|
				R:		SAY(Node$n), 
    			G:		Node$n.a,
				M: 		Node$n.b,
    			O:		Node$n.c;
		FI;
    	OD;

}
;


SHOW direct_messages SORT;
SHOW relayed_messages SORT;

CLEAR messages;
CLEAR direct_messages;
CLEAR relayed_messages;
