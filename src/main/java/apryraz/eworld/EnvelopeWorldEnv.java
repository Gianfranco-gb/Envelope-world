

package apryraz.eworld;

import java.util.ArrayList;



public class EnvelopeWorldEnv {
/**
   world dimension

**/
    String[] locations;
  int  WorldDim;


/**
*  Class constructor
*
* @param dim dimension of the world
* @param envelopeFile File with list of envelopes locations
**/
  public EnvelopeWorldEnv( int dim, String envelopeFile ) {

    WorldDim = dim;
    loadEnvelopeLocations(envelopeFile);
  }

/**
*   Load the list of pirates locations
*  
*    @param: name of the file that should contain a
*            set of envelope locations in a single line.
**/
  public void loadEnvelopeLocations( String envelopeFile ) {
      locations = envelopeFile.split(" ");
  }


/**
* Process a message received by the EFinder agent,
* by returning an appropriate answer
* It should answer to moveto and detectsat messages
*
* @param   msg message sent by the Agent
*
* @return  a msg with the answer to return to the agent
**/
   public AMessage acceptMessage( AMessage msg ) {
       AMessage ans = new AMessage("voidmsg", "", "", "" );

         msg.showMessage();
       if ( msg.getComp(0).equals("moveto") ) {
           int nx = Integer.parseInt( msg.getComp(1) );
           int ny = Integer.parseInt( msg.getComp(2) );
           
           if (withinLimits(nx,ny))
           {
             
             
             ans = new AMessage("movedto",msg.getComp(1),msg.getComp(2), "" );
           }
           else
             ans = new AMessage("notmovedto",msg.getComp(1),msg.getComp(2), "");

       } else {
           if(msg.getComp(0).equals("detectsat")){
               int x = Integer.parseInt(msg.getComp(1));
               int y = Integer.parseInt(msg.getComp(2));
               String message = EnvelopeLocation(x, y);
           }
             // YOU MUST ANSWER HERE TO THE OTHER MESSAGE TYPE:
             //   ( "detectsat", "x" , "y", "" )
             //
         }
       return ans;

   }





   public String EnvelopeLocation(int Ax, int Ay, int Ex, int Ey){
       if (Ax < Ex && Ay < Ey){

       }

   }


 /**
  * Check if position x,y is within the limits of the
  * WorldDim x WorldDim   world
  *
  * @param x  x coordinate of agent position
  * @param y  y coordinate of agent position
  *
  * @return true if (x,y) is within the limits of the world
  **/
   public boolean withinLimits( int x, int y ) {

    return ( x >= 1 && x <= WorldDim && y >= 1 && y <= WorldDim);
  }
 
}
