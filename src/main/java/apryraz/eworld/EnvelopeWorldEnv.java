

package apryraz.eworld;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;


public class EnvelopeWorldEnv {
/**
   world dimension

**/
    String[] locations;
    int WorldDim;
    String[] lectures = new String[5];
    String lecturesString;

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
      try{
          File myObjt = new File(envelopeFile);
          Scanner myreader = new Scanner(myObjt);

          while(myreader.hasNextLine()){
              String data = myreader.nextLine();
              locations = data.split(" ");
          }
          myreader.close();
      } catch (FileNotFoundException e) {
          e.printStackTrace();
      }
//      locations = envelopeFile.split(" ");
//      for (int i = 0; i <locations.length; i++) {
//         System.out.println(locations[i]);
//      }
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
               InitializeLectures();
               Allenvelops(x,y);
               ConverLecturesString();
               ans = new AMessage("detectsat", msg.getComp(1), msg.getComp(2), lecturesString );
           }
             // YOU MUST ANSWER HERE TO THE OTHER MESSAGE TYPE:
             //   ( "detectsat", "x" , "y", "" )
             //
         }
       return ans;

   }

    public void InitializeLectures(){
       for(int i = 0; i<lectures.length; i++){
           lectures[i] = "0";
       }

    }

    public void ConverLecturesString(){
       lecturesString = "0";
       for(int i = 0; i<lectures.length; i++){
           lecturesString = lecturesString+ lectures[i];
       }
    }

   public void Allenvelops (int x, int y){
       //System.out.println("locations:" +locations);
       for( int i = 0; i < locations.length; i++){
           String envelope = locations[i];
           int Ex = Integer.parseInt(String.valueOf(envelope.charAt(0)));
           int Ey = Integer.parseInt(String.valueOf(envelope.charAt(2)));
           EnvelopeLocation(x,y, Ex, Ey);
       }
       //for(int i = 0; i <lectures.length; i++){
       //    System.out.println(lectures[i]);
      // }
   }




   public void EnvelopeLocation(int Ax, int Ay, int Ex, int Ey){
       if (((Ax+1 == Ex) && (Ay-1 == Ey)) || ((Ax+1 == Ex) && (Ay == Ey)) || ((Ax+1 == Ex) && (Ay+1 == Ey))){
           lectures[0] = "1";
       }
       if(((Ax+1 == Ex) && (Ay+1 == Ey)) || ((Ax == Ex) && (Ay+1 == Ey)) || ((Ax-1 == Ex) && (Ay+1 == Ey))){
           lectures[1] = "1";
       }
       if(((Ax-1 == Ex) && (Ay-1 == Ey)) || ((Ax-1 == Ex) && (Ay == Ey)) || ((Ax-1 == Ex) && (Ay+1 == Ey))){
           lectures[2] = "1";
       }
       if(((Ax+1 == Ex) && (Ay-1 == Ey)) || ((Ax == Ex) && (Ay-1 == Ey)) || ((Ax-1 == Ex) && (Ay-1 == Ey ))){
           lectures[3] = "1";
       }
       if(Ax == Ex && Ay == Ey){
           System.out.println("hola");
           lectures[4] = "1";
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
