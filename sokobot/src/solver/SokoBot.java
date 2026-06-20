package solver;

import java.util.LinkedList; // used for: BFS in distance table computation
import java.util.Queue; // used for: BFS in distance table computation
import java.util.List;        // used for: passing box positions around
import java.util.Arrays;      // used for: sorting + hashing the box arrays in State

public class SokoBot {

    /**
     * Maximum width of puzzle grid.
     */
    private int width;

    /**
     * Maximum height of puzzle grid.
     */
    private int height;

    /**
     * 2D Matrix that stores the static walls of the current sokoban puzzle.
     * - True indicates a wall (unpassable space). Otherwise,
     * - False indicates a passable space, a box, the player bot, or a goal.
     */
    private boolean[][] walls;

    /**
     * 2D Matrix mapping target positions for the boxes.
     * - True indicates a goal is located at the grid coordinates.
     * - False indicates a non-goal space.
     */
    private boolean[][] goals;

    /**
     * 2D Matrix that stores the dead squares of the current sokoban puzzle.
     * - True indicates that the cell is a non-goal space that would make the puzzle unsolvable if boxes are pushed onto them.
     * - False indicates that the cell is either safe for a box or is a goal.
     */
    private boolean[][] deadSquares;

    /**
     * 2D Distance Matrix for Min-Push Heuristic calculation.
     */
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

    /**
     * ===========================================================================================
     * PART 1: BOARD REPRESENTATION AND PREPROCESSING
     * - initialize(): gets how the board looks like
     * - computeDeadSquares(): marks non goal corner cells as dead squares cus any box pushed into those cells can never be moved into a goal
     * - computeBoxGoalDistances(): computes backwards from a goal that results in a table that has a lower bound on how many pushes a box needs to reach each goal
     * ============================================================================================
     */

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
                boolean wallWest = (c - 1 >= 0) && walls[r][c - 1];
                boolean wallEast = (c + 1 < width) && walls[r][c + 1];

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
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {

                if (!deadSquares[r][c] || goals[r][c]) { //start dead corridor detection only if it's a dead corner or a non-goal
                    continue;
                }

                int column = c + 1; // scan to the right
                boolean goalDetected = false;

                while (column < width && !walls[r][column]) { // traverse until a wall is reached
                    if (goals[r][column]) {
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
                    queue.add(new int[]{r, c});
                } //then, load to queue
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

    /**
     * ===========================================================================================
     * PART 2: PLAYER MOVEMENT AND STATE REPRESENTATION
     * - occupied(): quick check if a cell is blocked for the player (wall or box)
     * - findReachable(): BFS that checks every cell the player can walk to without pushing a box
     * - canonicalPlayer(): collapses the player's whole reachable region down to one cell
     * - pathTo(): BFS that rebuilds the actual u/d/l/r moves to walk from one cell to another
     * - Reach (class): the result of findReachable (reachable grid + canonical cell)
     * - State (class): one search node (box layout + canonical player) with equals/hashCode
     * ============================================================================================
     */

    // its blocked if its off the grid, a wall, or one of the boxes is sitting on it.
    // goals dont block the player
    private boolean occupied(List<int[]> boxes, int r, int c) {
        if (r < 0 || r >= height || c < 0 || c >= width) {
            return true; // off-grid counts as blocked so no need to bounds-check everywhere else
        }
        if (walls[r][c]) {
            return true;
        }
        for (int[] box : boxes) {
            if (box[0] == r && box[1] == c) {
                return true;
            }
        }
        return false;
    }

    private Reach findReachable(List<int[]> boxes, int playerR, int playerC) {
        boolean[][] reachable = new boolean[height][width];
        Queue<int[]> queue = new LinkedList<>();

        reachable[playerR][playerC] = true;
        queue.add(new int[]{playerR, playerC});

        // canonical = top left most cell in the whole region. start it at the player, then update it.
        int[] canonical = new int[]{playerR, playerC};

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};

        while (!queue.isEmpty()) { // loops until the whole region is checked
            int[] current = queue.poll();
            int currRow = current[0];
            int currCol = current[1];

            for (int i = 0; i < 4; i++) { // check the current tile's neighbors
                int nextRow = currRow + dRow[i];
                int nextCol = currCol + dCol[i];

                if (occupied(boxes, nextRow, nextCol)) { // skip walls, boxes, off grid
                    continue;
                }
                if (reachable[nextRow][nextCol]) { // skip tiles already checked
                    continue;
                }

                reachable[nextRow][nextCol] = true; // mark as reachable, then load to queue
                queue.add(new int[]{nextRow, nextCol});

                // update canonical if we found a cell higher up, or further left on the same row
                if (nextRow < canonical[0] || (nextRow == canonical[0] && nextCol < canonical[1])) {
                    canonical[0] = nextRow;
                    canonical[1] = nextCol;
                }
            }
        }

        return new Reach(reachable, canonical);
    }

    private int[] canonicalPlayer(List<int[]> boxes, int playerR, int playerC) {
        return findReachable(boxes, playerR, playerC).canonical;
    }


    private String pathTo(List<int[]> boxes, int fromR, int fromC, int toR, int toC) {
        if (fromR == toR && fromC == toC) {
            return ""; // already there, no moves needed
        }

        boolean[][] visited = new boolean[height][width];
        int[][] parentRow = new int[height][width]; // tracks which row i came from
        int[][] parentCol = new int[height][width]; // tracks which col i came from

        Queue<int[]> queue = new LinkedList<>();

        visited[fromR][fromC] = true;
        queue.add(new int[]{fromR, fromC});

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};

        boolean found = false;
        while (!queue.isEmpty() && !found) {
            int[] current = queue.poll();
            int currRow = current[0];
            int currCol = current[1];

            for (int i = 0; i < 4; i++) {
                int nextRow = currRow + dRow[i];
                int nextCol = currCol + dCol[i];

                if (occupied(boxes, nextRow, nextCol)) { // skip walls/boxes/off-grid
                    continue;
                }
                if (visited[nextRow][nextCol]) { // already reached on an equal-or-shorter path, skip
                    continue;
                }

                visited[nextRow][nextCol] = true;
                parentRow[nextRow][nextCol] = currRow; // remember where this tile came from
                parentCol[nextRow][nextCol] = currCol;

                if (nextRow == toR && nextCol == toC) { // hit the target, stop early
                    found = true;
                    break;
                }
                queue.add(new int[]{nextRow, nextCol});
            }
        }

        if (!visited[toR][toC]) {
            return null; // target wasnt reachable (shouldnt happen for tiles inside the region)
        }

        // walk the parent chain from target back to start, collecting moves in reverse
        StringBuilder reversed = new StringBuilder();
        int curR = toR;
        int curC = toC;

        while (curR != fromR || curC != fromC) {
            int pR = parentRow[curR][curC];
            int pC = parentCol[curR][curC];

            reversed.append(stepChar(pR, pC, curR, curC));
            curR = pR;
            curC = pC;
        }

        return reversed.reverse().toString(); // flip it so it reads start -> target
    }

    // turns one single-tile step (from -> to) into its move letter.
    private char stepChar(int fromR, int fromC, int toR, int toC) {
        if (toR == fromR - 1) return 'u';
        if (toR == fromR + 1) return 'd';
        if (toC == fromC - 1) return 'l';
        return 'r'; // only case left: toC == fromC + 1
    }

    private static class Reach {
        // reachable[r][c] == true means the player can walk there without pushing a box.
        final boolean[][] reachable;
        // the single representative cell for the whole region (the top-left most).
        final int[] canonical;

        Reach(boolean[][] reachable, int[] canonical) {
            this.reachable = reachable;
            this.canonical = canonical;
        }
    }

    private static class State {
        final int[][] boxes;     // sorted 2D array of box coordinates
        final int playerR;       // canonical player row
        final int playerC;       // canonical player column
        private final int hash;  // cached so hashCode() stays fast (O(1))

        State(List<int[]> boxList, int playerR, int playerC) {
            // pull the boxes into a 2D array and sort them by row first, then column
            int[][] boxArray = new int[boxList.size()][2];
            for (int i = 0; i < boxList.size(); i++) {
                boxArray[i][0] = boxList.get(i)[0];
                boxArray[i][1] = boxList.get(i)[1];
            }
            Arrays.sort(boxArray, (a, b) -> {
                if (a[0] != b[0]) return Integer.compare(a[0], b[0]);
                return Integer.compare(a[1], b[1]);
            });

            this.boxes = boxArray;
            this.playerR = playerR;
            this.playerC = playerC;
            this.hash = computeHash(boxArray, playerR, playerC);
        }

        private static int computeHash(int[][] boxes, int playerR, int playerC) {
            int h = Arrays.deepHashCode(boxes);
            h = 31 * h + playerR;
            h = 31 * h + playerC;
            return h;
        }

        @Override
        public int hashCode() {
            return hash;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) return true;
            if (!(other instanceof State)) return false;
            State s = (State) other;

            return this.playerR == s.playerR &&
                    this.playerC == s.playerC &&
                    Arrays.deepEquals(this.boxes, s.boxes);
        }
    }
}