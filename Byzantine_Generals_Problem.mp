/*-------------------------------------------------------------------------------
Model of the Byzantine Generals Problem  

Created by:
John Phillips in November 2023

Edited by:
John Phillips in October 2024

Purpose:


Description: 

   
Assumptions:
1. The order is attack. 
2. All messages sent are received. 
3. All messages cannot be changed in transit. 

Instructions:

Trace Count: 128 traces at Scope 1, 7 Generals, 1-7 Traitor
Elapsed time: 70.58 sec

TODOs: 
1. Implement tie breaker. I think this is present but need to confirm. 
2. Figure out how to find and remove mirror outcomes to speed up trace generation. 
3. Explore code for ways to speed up trace generation. 
-------------------------------------------------------------------------------*/ 

SCHEMA Byzantine_Generals_Problem

/* Placeholder variables to hold trace information. */
ATTRIBUTES { number a, b, c, d, e, f; };

ATTRIBUTES { number count, Generals, General_ID, Majority, Order, Orders, Traitor, Traitors; };

/* 1 = Attack
   0 = Retreat */
Orders := 1;

Generals := 7; 
Traitors := 4;

Majority := Generals / 2 + 0.5;

/* Used to track trace versions over time. */
SAY ( "Version 2024-10-16" );

/* Mark each trace with the trace number. */
SAY ( "Trace " trace_id );

ROOT Army: 
	{+<7..7> General +}

BUILD {
	General_ID := 1;

	COORDINATE  $a: General
		DO 
			$a.General_ID := General_ID; 
			General_ID +:= 1; 
		OD;   
}
;

	General:
		( 
        	( Attack | Retreat )
            Exchange_Messengers
        ( _Attack | _Retreat )
		)		
	;

/* Set the Order and find the Traitor(s) based on the Orders. */
count := 0;

COORDINATE	$a: General
	DO COORDINATE $b: ( Attack | Retreat ) FROM $a
		DO IF $b IS Attack THEN 
			$a.Order := 1; 
			IF Orders == 0 THEN
				$a.Traitor := 1; count +:= 1;
				/*ADD SAY("Traitor") PRECEDES $a;*/
			FI; 
		   FI;
		   
		   IF $b IS Retreat THEN
		   	$a.Order := 0;
			IF Orders == 1 THEN
				$a.Traitor := 1; count +:= 1;
				/*ADD SAY("Traitor") PRECEDES $a;*/
			FI; 		   	
		 FI; OD;
	OD;

/* Set the max number of Traitors. */
/*IF count != Traitors THEN REJECT; FI;*/

count := 0;

GRAPH messages { };

WITHIN messages {
	COORDINATE  $a: General		
		DO COORDINATE $b: General
		   	DO 		
    				/* What they said happened. */
    				Node$y: NEW ( "Node" );
    				Node$y.a := ( $a.General_ID );
				Node$y.b := ( $b.General_ID );
    				IF $a.Traitor == 1 THEN
 					IF Orders == 1 THEN Node$y.c := 0; FI;
 					IF Orders == 0 THEN Node$y.c := 1; FI;
	
    				ELSE
    					Node$y.c := ( $b.Order );    							
    				FI;	
    				/* Keep track of the number of "Attack" orders. */
    				count +:= Node$y.c;										  										
    			OD;	
    			/*ADD SAY(count "|" Majority) PRECEDES $a;*/
    			count := 0;		
		OD;  
}
;

count := 0;

COORDINATE	$a: General
	DO count +:= $a.Order; OD;

IF ( count >= Majority ) THEN 
	IF #_Retreat > 0 THEN 
	CLEAR messages;
	REJECT; 
	FI;
FI;
IF ( count < Majority ) THEN  
	IF #_Attack > 0 THEN 
	CLEAR messages;
	REJECT; 
	FI; 
FI;

/* General G received a message from General M with order O. */
TABLE relayed_messages {
	TITLE ("Trace " trace_id " Message Results");
	TABS 	number G,
			number M,
    			number O;
}
;

WITHIN messages {
    FOR Node$n
    	DO   		
		relayed_messages <|
    			G:		Node$n.a,
			M: 		Node$n.b,
    			O:		Node$n.c;
    	OD;

}
;

SHOW relayed_messages;

CLEAR messages;
CLEAR relayed_messages;