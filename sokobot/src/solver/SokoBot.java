package solver;

import java.util.LinkedList; // used for: BFS in distance table computation
import java.util.Queue; // used for: BFS in distance table computation

public class SokoBot {

    /** Maximum width of puzzle grid. */
    private int width;
    
    /** Maximum height of puzzle grid. */
    private int height;
    
    /** 2D Matrix that stores the static walls of the current sokoban puzzle. 
     *    - True indicates a wall (unpassable space). Otherwise,
     *    - False indicates a passable space, a box, the player bot, or a goal. 
     */
    private boolean[][] walls;
    
    /** 2D Matrix mapping target positions for the boxes. 
     *    - True indicates a goal is located at the grid coordinates.
     *    - False indicates a non-goal space.
    */
    private boolean[][] goals;

    /** 2D Matrix that stores the dead squares of the current sokoban puzzle. 
     *    - True indicates that the cell is a non-goal space that would make the puzzle unsolvable if boxes are pushed onto them.
     *    - False indicates that the cell is either safe for a box or is a goal. 
    */
    private boolean[][] deadSquares;

    /** 2D Distance Matrix for Min-Push Heuristic calculation.  */
    private int[][] distanceTable;


  public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {
    /*
     * YOU NEED TO REWRITE THE IMPLEMENTATION OF THIS METHOD TO MAKE THE BOT SMARTER
     */
    /*
     * Default stupid behavior: Think (sleep) for 3 seconds, and then return a
     * sequence
     * that just moves left and right repeatedly.
     */
    try {
      Thread.sleep(3000);
    } catch (Exception ex) {
      ex.printStackTrace();
    }
    return "lrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlrlr";
  }

  /** ===========================================================================================
   * PART 1: BOARD REPRESENTATION AND PREPROCESSING 
   *    - initialize(): gets how the board looks like 
   *    - computeDeadSquares(): marks non goal corner cells as dead squares cus any box pushed into those cells can never be moved into a goal
   *    - computeBoxGoalDistances(): computes backwards from a goal that results in a table that has a lower bound on how many pushes a box needs to reach each goal
   * ============================================================================================*/

  private void initialize(int width, int height, char[][] mapData, char[][] itemsData) {

      this.width = width;
      this.height = height;

      // instantiate the walls and goals matrices based on the map data
      this.walls = new boolean[height][width];
      this.goals = new boolean[height][width];

      // main loop for puzzle board parsing
      for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                char staticTile = mapData[r][c];
                
                //case 1: wall detection (set walls[r][c] to true if there is a wall at (r, c))
                if (staticTile == '#') {
                    this.walls[r][c] = true;
                } 
                //case 2: goal detection (set goals[r][c] to true if there is a goal at (r, c))
                else if (staticTile == '.') {
                    this.goals[r][c] = true;
                }
            }
      }

      computeDeadSquares(); //based on the extracted walls and goals, compute the dead squares of the puzzle to avoid.
      computeBoxGoalDistances(); //based on the extracted walls and goals, compute the distance table for the min-push heuristic.

  }

  private void computeDeadSquares() {

    this.deadSquares = new boolean[height][width];

    //Case 1: Dead Corner Detection (mark every corner that is a non-goal square as a dead square, since any box pushed into that cell can never be moved into a goal.)
    for (int r = 0; r < height; r++) {
        for (int c = 0; c < width; c++) {       
            // Exclude coordinates holding blocking structures or valid goals
            if (walls[r][c] || goals[r][c]) {
                continue;
            }
            
            boolean wallNorth = (r - 1 >= 0) && walls[r - 1][c];
            boolean wallSouth = (r + 1 < height) && walls[r + 1][c];
            boolean wallWest  = (c - 1 >= 0) && walls[r][c - 1];
            boolean wallEast  = (c + 1 < width) && walls[r][c + 1];
            
            // Mark the tile as a dead square if it is a corner 
            if ((wallNorth && wallEast) || 
                (wallEast && wallSouth) || 
                (wallSouth && wallWest) || 
                (wallWest && wallNorth)) {
                
                this.deadSquares[r][c] = true; 
            }
        }
    }

    //Case 2: Dead Square Detection (mark every non-goal square that is in a dead-square corridor, except for corridors that have goals)
    for (int r = 0; r < height; r++){
      for (int c = 0; c < width; c++) {

        if (!deadSquares[r][c] || goals[r][c]) { //start dead corridor detection only if it's a dead corner or a non-goal
            continue; 
        }

        int column = c+1; // scan to the right
        boolean goalDetected = false; 

        while (column < width && !walls[r][column]) { // traverse until a wall is reached 
          if (goals[r][column]){
            goalDetected = true;
            break; // if goal has been detected, do not mark the corridor as a dead corridor
          }

          if (deadSquares[r][column]) { 
            boolean wallNorth = true;
            boolean wallSouth = true;

            for (int check = c; check <= column; check++) { //corridor is only valid if atleast one side of the corridor is a continuous wall (for it to be completely dead)
                // check if wall above is broken 
                if (r - 1 < 0 || !walls[r - 1][check]) {
                    wallNorth = false;
                }
                // check if wall below is broken
                if (r + 1 >= height || !walls[r + 1][check]) {
                    wallSouth = false;
                }
            }

            if (!goalDetected && (wallNorth || wallSouth)) {
                for (int dead = c; dead <= column; dead++) { 
                    deadSquares[r][dead] = true; 
                }
            }
            break; 
        }     
        column++;
      }
    }

  }

}    

  private void computeBoxGoalDistances() {
    
    this.distanceTable = new int[height][width]; //setup distance table, assume every tile is unreachable
    
    for (int r = 0; r < height; r++) {
        for (int c = 0; c < width; c++) {
            this.distanceTable[r][c] = Integer.MAX_VALUE; 
        }
    }

    Queue<int[]> queue = new LinkedList<>();

    for (int r = 0; r < height; r++) {
        for (int c = 0; c < width; c++) {
            if (goals[r][c]) {
                this.distanceTable[r][c] = 0; //locate all goals and set distance value to 0  
                queue.add(new int[]{r, c});} //then, load to queue
          }
      }

    int[] dRow = {-1, 1, 0, 0};
    int[] dCol = {0, 0, -1, 1};

      while (!queue.isEmpty()) { //will loop until every tile has been evaluated 
        int[] current = queue.poll();
        int currRow = current[0];
        int currCol = current[1];
        int currentDist = this.distanceTable[currRow][currCol];

          for (int i = 0; i < 4; i++) { // check the current cell's neighboring tiles (using direction vectors)
              
              int nextRow = currRow + dRow[i];
              int nextCol = currCol + dCol[i];

              if (nextRow >= 0 && nextRow < height && nextCol >= 0 && nextCol < width) {
                  if (walls[nextRow][nextCol]) { //skip if neighboring tile is a wall
                      continue;
                  }

                  if (currentDist + 1 < this.distanceTable[nextRow][nextCol]) { //if shorter path is found, update distance table and push neighbor to the queue
                      this.distanceTable[nextRow][nextCol] = currentDist + 1;
                      queue.add(new int[]{nextRow, nextCol});
                  }
              }
          }
      }
    }
  
  
  







  
  
  }