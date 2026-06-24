package solver;

import java.util.ArrayDeque; // used for: BFS in distance table computation
import java.util.ArrayList; // used for: BFS in distance table computation
import java.util.Arrays;        // used for: passing box positions around
import java.util.Comparator;   // used for: building successor box configurations
import java.util.HashMap;      // used for: sorting + hashing the box arrays in State
import java.util.HashSet; // used for: the A* open list
import java.util.LinkedList;    // used for: ordering nodes in the open list by lexicographic cost
import java.util.List;       // used for: best-known-cost bookkeeping (open list dedup)
import java.util.PriorityQueue;       // used for: the A* closed list
import java.util.Queue;    // used for: reconstructing the move string in buildPath()

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
    private int[][][] pushDist;  // [numGoals][height][width]
    private int[][]   goalPos;   // goalPos[i] = {row, col}
    private int       numGoals;


    /**
     * Drives the whole solve: parses the puzzle's dynamic items, then runs A* search over
     * the push-based state space (see {@link #expand} and PART 4 below) until a solved
     * configuration is found or the time/node budget runs out.
     * <p>
     * Two cost components are tracked per search node, compared lexicographically:
     * pushes first (the conventional Sokoban notion of an optimal solution, and the one the
     * heuristic in PART 3 actually bounds), then total real keypresses as a tie-break so that,
     * among multiple routes that all use the minimum number of pushes, the one needing the
     * least walking in between is preferred. See {@link Node} and {@link #expand} for exactly
     * how this is enforced.
     *
     * @param width     width of the puzzle grid
     * @param height    height of the puzzle grid
     * @param mapData   static layout ({@code '#'} walls, {@code '.'} goals)
     * @param itemsData dynamic layout ({@code '@'} player, {@code '$'} boxes)
     * @return a string of {@code u}/{@code d}/{@code l}/{@code r} moves that solves the puzzle,
     *         or {@code ""} if no solution could be found within the time/node budget
     */
    public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {

        // Self-imposed budget, comfortably under the harness's hard 15s cutoff. Checked
        // periodically inside the search loop so a pathological level can't hang forever.
        long deadline = System.nanoTime() + 14_000_000_000L;

        initialize(width, height, mapData, itemsData);

        // --- parse the dynamic items: the player's start cell and every box ---
        List<int[]> boxes = new ArrayList<>();
        int startPlayerR = -1;
        int startPlayerC = -1;

        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                char itemTile = itemsData[r][c];
                if (itemTile == '$') {
                    boxes.add(new int[]{r, c});
                } else if (itemTile == '@') {
                    startPlayerR = r;
                    startPlayerC = c;
                }
            }
        }

        if (isDeadlocked(boxes)) {
            return ""; // already unsolvable from the start position, no point searching at all
        }

        // --- A* bookkeeping ---
        // Lexicographic ordering: primary key is f = g + h (pushes), so the search remains
        // provably push-optimal. Only once two nodes are TIED on f (and on h -- for a goal node
        // h is always 0, so any two push-tied solutions are tied here too) does totalMoves break
        // the tie, so the cheaper-to-walk route among equally-pushed solutions wins, rather than
        // whichever one happens to come off Java's heap first.
        int[] canonicalStart = canonicalPlayer(boxes, startPlayerR, startPlayerC);
        State startState = new State(boxes, canonicalStart[0], canonicalStart[1]);

        PriorityQueue<Node> open = new PriorityQueue<>(
                Comparator.<Node>comparingInt(n -> n.g + n.h)
                        .thenComparingInt(n -> n.h)
                        .thenComparingInt(n -> n.totalMoves)
        );
        // bestCost tracks the lexicographic (pushes, totalMoves) pair per state, packed into a
        // single long so two states can be compared with one numeric comparison. totalMoves is
        // bounded well under 1,000,000 by the time/node budget below, so this packing is safe.
        HashMap<State, Long> bestCost = new HashMap<>();
        HashSet<State> closed = new HashSet<>();

        Node startNode = new Node(startState, startPlayerR, startPlayerC, 0, 0, heuristic(boxes), null, "");
        open.add(startNode);
        bestCost.put(startState, packCost(0, 0));

        // Hard safety valve on memory/time independent of the wall-clock check, in case a
        // level's reachable state space is enormous (mainly a concern for dense 8-box levels).
        final int MAX_NODES = 2_000_000;
        int nodesExpanded = 0;

        while (!open.isEmpty()) {

            if (nodesExpanded > MAX_NODES || System.nanoTime() > deadline) {
                return ""; // out of budget; let the harness report "took too long" instead of returning a guess
            }

            Node current = open.poll();

            if (closed.contains(current.state)) {
                continue; // stale duplicate left behind by lazy deletion from the open list
            }
            closed.add(current.state);
            nodesExpanded++;

            List<int[]> currentBoxes = stateToBoxList(current.state);

            if (isSolved(currentBoxes)) {
                return buildPath(current);
            }

            expand(current, currentBoxes, open, bestCost, closed);
        }

        return ""; // open list exhausted with no goal found: this level is unsolvable
    }

    /**
     * ===========================================================================================
     * PART 1: BOARD REPRESENTATION AND PREPROCESSING
     * - initialize(): gets how the board looks like
     * - computeDeadSquares(): marks non goal corner cells as dead squares cus any box pushed into those cells can never be moved into a goal
     * - computeBoxGoalDistances(): computes backwards from a goal that results in a table that has a lower bound on how many pushes a box needs to reach each goal
     * ============================================================================================
     */

    /**
     * Initializes the puzzle board representation of the Sokoban puzzle
     * 
     * <p> This method parses the map data to classify which tiles of the puzzle 
     * are walls or goals before storing them in their dedicated 2D matrices. Once the
     * basic board information is extracted, the preprocessing methods computeDeadSquares() 
     * and computeBoxGoalDistances() are called, both of which implemented to help the solver 
     * further on in the program as it searches for a solution to the puzzle. </p>
     * 
     * @param width the width of the puzzle board
     * @param height the height of the puzzle board
     * @param mapData the board layout containing walls and goals of the current Sokoban puzzle 
     * @param itemsData the board layout containing the player and the boxes of the current Sokoban puzzle
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
        computeAllPushDistances();
        computeBoxGoalDistances(); //based on the extracted walls and goals, compute the distance table for the min-push heuristic.

    }

    /**
     * Classifies which tiles are dead squares on the Sokoban board and marks them through a 2D matrix
     * 
     * <p> A dead square is any non-goal tile in the board which can make the puzzle unsolvable
     * once a box is pushed onto that position. Marking the dead squares of the puzzle during
     * the preprocessing stage allows the solver to avoid moves that would inevitably lead to an unsolvable state. </p>
     * 
     * <p> Two cases of dead squares are detected in this method. First, it loops through the board
     * to mark dead corners, which are all non-goal tiles that are adjacent to walls on two
     * perpendicular sides. Second, it scans the board again to identify dead corridors which are sequences
     * of non-goal tiles between two dead corners that lie along a continuous wall and contain no goal tiles. </p>
     * 
     * <p> The dead-square statuses of the tiles are stored in the {@code deadSquares} matrix, where tiles marked 
     * {@code true} indicates that the solver should avoid that tile while searching for a path. </p>
     */
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

              if (!deadSquares[r][c] || goals[r][c]) { //start only if it is already marked as a dead square and is not a goal
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

      for (int r = 0; r < height; r++) {
          for (int c = 0; c < width; c++) {

            if (!deadSquares[r][c] || goals[r][c]) { //start only if it is already marked as a dead square and is not a goal
              continue;
            }

            int row = r + 1;
            boolean goalDetected = false;

            while (row < height && !walls[row][c]) {

                if (goals[row][c]) {
                    goalDetected = true;
                    break;
                }

                if (deadSquares[row][c]) {
                    boolean wallWest = true;
                    boolean wallEast = true;

                    for (int check = r; check <= row; check++) {
                      // Check if left wall is continuous
                      if (c - 1 < 0 || !walls[check][c - 1]) {
                          wallWest = false;
                      }
                      // Check if right wall is continuous
                      if (c + 1 >= width || !walls[check][c + 1]) {
                          wallEast = false;
                      }
                    }

                    if (!goalDetected && (wallWest || wallEast)) {
                        for (int dead = r; dead <= row; dead++) {
                            deadSquares[dead][c] = true;
                        }
                    }
                    break;
                }
                row++;
              }
          }
      }
    }

    /**
     * Computes the distance from every reachable tile on the board to the nearest 
     * goal tile
     * 
     * <p> The second method of the preprocessing phase performs a BFS starting from all goal
     * locations simulataneously. Each goal is assigned to a distance value of {@code 0}, and neighboring
     * tiles are explored in order of increasing distance.</p> 
     * 
     * <p> The resulting distances are stored in the 2D matrix {@code distanceTable}. For every
     * reachable tile, the recorded value represents the length of the shortest path found to a 
     * nearest goal tile. Tiles that cannot reach any goal remain assigned {@code Integer.MAX_VALUE}.
     * The resulting distance table of this method will be later used by the solver to determine 
     * which boxes are positioned closer to goal tiles.</p>
     */
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

    /**
     * Checks whether a tile cannot be stood on or walked through by the player.
     * A tile is blocked if it lies outside the grid, holds a wall, or has a box on it.
     * Goal tiles are not blocked, since the player is allowed to stand on them.
     *
     * @param boxes the current positions of all boxes, each as an {@code int[]} of {row, col}
     * @param r     the row of the tile to check
     * @param c     the column of the tile to check
     * @return {@code true} if the tile is off-grid, a wall, or occupied by a box; {@code false} otherwise
     */
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

    /**
     * Floods outward from the player using a breadth-first search to find every tile the player
     * can reach without pushing a box, stopping at walls and boxes. While flooding, it also tracks
     * the top-left-most reachable tile, which serves as the region's canonical representative.
     *
     * @param boxes   the current positions of all boxes, each as an {@code int[]} of {row, col}
     * @param playerR the player's starting row
     * @param playerC the player's starting column
     * @return a {@link Reach} holding the grid of reachable tiles and the canonical cell
     */
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

    /**
     * Returns the canonical (representative) tile for the region the player can currently reach.
     * Two positions with identical boxes but the player on different but connected tiles are the
     * same situation, so collapsing the whole reachable region to one fixed tile keeps the search
     * from treating them as distinct states. This is a convenience wrapper around
     * {@link #findReachable}, which computes the canonical cell as it floods.
     *
     * @param boxes   the current positions of all boxes, each as an {@code int[]} of {row, col}
     * @param playerR the player's current row
     * @param playerC the player's current column
     * @return the canonical cell as an {@code int[]} of {row, col}
     */
    private int[] canonicalPlayer(List<int[]> boxes, int playerR, int playerC) {
        return findReachable(boxes, playerR, playerC).canonical;
    }

    /**
     * Rebuilds the actual move string ('u', 'd', 'l', 'r') the player must walk to get from one tile
     * to another without pushing any box. It runs a breadth-first search that records the tile each
     * position was reached from, then traces that parent chain backward from the target to the start
     * and reverses it so the moves read in forward order. Used when assembling the final solution,
     * since the player must physically walk to a box before it can push it.
     *
     * @param boxes the current positions of all boxes, each as an {@code int[]} of {row, col}
     * @param fromR the starting row
     * @param fromC the starting column
     * @param toR   the destination row
     * @param toC   the destination column
     * @return the move string from start to destination, an empty string if they are the same tile,
     *         or {@code null} if the destination is unreachable
     */
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

    /**
     * Converts a single one-tile step between adjacent tiles into its move letter. Assumes the two
     * tiles differ by exactly one orthogonal step.
     *
     * @param fromR the row of the tile being moved from
     * @param fromC the column of the tile being moved from
     * @param toR   the row of the tile being moved to
     * @param toC   the column of the tile being moved to
     * @return 'u', 'd', 'l', or 'r' for the direction of the step
     */
    private char stepChar(int fromR, int fromC, int toR, int toC) {
        if (toR == fromR - 1) return 'u';
        if (toR == fromR + 1) return 'd';
        if (toC == fromC - 1) return 'l';
        return 'r'; // only case left: toC == fromC + 1
    }

    /**
     * Bundles the two outputs of {@link #findReachable}: the grid of reachable tiles and the
     * region's canonical cell, so both can be returned together from a single call.
     */
    private static class Reach {
        /** {@code reachable[r][c] == true} means the player can walk there without pushing a box. */
        final boolean[][] reachable;
        /** The single representative cell for the whole region (the top-left-most one). */
        final int[] canonical;

        /**
         * @param reachable the grid marking which tiles the player can reach
         * @param canonical the region's representative cell as {row, col}
         */
        Reach(boolean[][] reachable, int[] canonical) {
            this.reachable = reachable;
            this.canonical = canonical;
        }
    }

    /**
     * One node in the search: a complete snapshot of a position, described by the box layout plus
     * the canonical player tile. Boxes are stored in a sorted array so two states with the same
     * boxes compare as equal regardless of order, and {@link #equals} and {@link #hashCode} are
     * overridden so states can be stored in a {@code HashSet} for fast "already visited?" checks.
     */
    private static class State {
        /** The box coordinates, sorted by row then column so equality is order-independent. */
        final int[][] boxes;
        /** The canonical player row. */
        final int playerR;
        /** The canonical player column. */
        final int playerC;
        /** Cached hash so {@link #hashCode} stays O(1) across repeated lookups. */
        private final int hash;

        /**
         * Builds a state from a raw box list and the canonical player tile. The boxes are copied
         * into a fixed array and sorted (row first, then column) so that identical layouts always
         * produce an identical array, and the hash is computed once up front.
         *
         * @param boxList the box positions, each as an {@code int[]} of {row, col}
         * @param playerR the canonical player row
         * @param playerC the canonical player column
         */
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

        /**
         * Computes a content-based hash combining the box layout and the canonical player position.
         * Uses {@link Arrays#deepHashCode} so the hash depends on the box values, not array identity.
         *
         * @param boxes   the sorted box coordinates
         * @param playerR the canonical player row
         * @param playerC the canonical player column
         * @return the combined hash code for the state
         */
        private static int computeHash(int[][] boxes, int playerR, int playerC) {
            int h = Arrays.deepHashCode(boxes);
            h = 31 * h + playerR;
            h = 31 * h + playerC;
            return h;
        }

        /**
         * @return the cached content-based hash code for this state
         */
        @Override
        public int hashCode() {
            return hash;
        }

        /**
         * Two states are equal when they share the same canonical player tile and the same box
         * layout (compared by content via {@link Arrays#deepEquals}).
         *
         * @param other the object to compare against
         * @return {@code true} if {@code other} is a state with the same player and boxes
         */
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

    /**
     * ===========================================================================================
     * PART 3: HEURISTICS AND DEADLOCK DETECTION
     * - heuristic(): A* h(n), wraps the goal-assignment lower bound
     * - assignmentLowerBound(): min-cost perfect matching of boxes to goals (Hungarian algorithm)
     * - isDeadlocked(): orchestrates freeze-deadlock + goal-assignment-feasibility checks
     * - isFrozen(): checks whether a single box can never be pushed again
     * - isBlockedOnAxis() / isBlockedSide(): freeze-deadlock helpers, one axis at a time
     * - hasGoalAssignment(): Hall's-theorem style feasibility check (perfect bipartite matching exists)
     * - isSolved(): every box currently sits on a goal
     *
     * KEY OPTIMIZATION over the original:
     *   The original called bfsPushDistanceFromBox() — a full O(height*width) BFS — inside both
     *   assignmentLowerBound() and hasGoalAssignment() on every generated successor node.
     *   With 5 boxes and 200,000 node expansions that is millions of BFS runs.
     *
     *   The fix: precompute pushDist[goalIndex][r][c] ONCE in initialize() by running one
     *   backwards BFS per goal.  During search every cost lookup becomes an O(1) table read.
     *   Two new fields are required in the enclosing class:
     *
     *       private int[][][] pushDist;   // [numGoals][height][width], filled by computeAllPushDistances()
     *       private int[][]   goalPos;    // goalPos[i] = {row, col} for goal i
     *       private int       numGoals;
     *
     *   Call computeAllPushDistances() from initialize(), after walls/goals are parsed.
     * ============================================================================================
     */

    // ------------------------------------------------------------------
    // PREPROCESSING — call this from initialize() after walls/goals ready
    // ------------------------------------------------------------------

    /**
     * Precomputes push distances from every board cell to every goal.
     * <p>
     * Runs one backwards BFS <em>per goal</em> over the box-push graph (walls block,
     * every non-wall step costs 1 push).  Stores results in {@code pushDist[g][r][c]}.
     * <p>
     * Total cost: O(numGoals * height * width) — paid once at startup.
     * Without this, the original code recomputed equivalent BFS data inside
     * {@code assignmentLowerBound} and {@code hasGoalAssignment} on every node expansion,
     * which was O(numBoxes * numGoals * height * width) <em>per node</em>.
     */
    private void computeAllPushDistances() {
        // Collect goal positions
        List<int[]> goalList = new ArrayList<>();
        for (int r = 0; r < height; r++)
            for (int c = 0; c < width; c++)
                if (goals[r][c]) goalList.add(new int[]{r, c});

        numGoals = goalList.size();
        goalPos  = goalList.toArray(new int[0][]);
        pushDist = new int[numGoals][height][width];

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};

        for (int g = 0; g < numGoals; g++) {
            int[][] dist = pushDist[g];
            for (int[] row : dist) Arrays.fill(row, Integer.MAX_VALUE);

            int gr = goalPos[g][0], gc = goalPos[g][1];
            dist[gr][gc] = 0;

            Queue<int[]> queue = new LinkedList<>();
            queue.add(new int[]{gr, gc});

            while (!queue.isEmpty()) {
                int[] cur  = queue.poll();
                int   cr   = cur[0], cc = cur[1];
                int   cd   = dist[cr][cc];

                for (int i = 0; i < 4; i++) {
                    int nr = cr + dRow[i], nc = cc + dCol[i];
                    if (nr < 0 || nr >= height || nc < 0 || nc >= width) continue;
                    if (walls[nr][nc]) continue;
                    if (cd + 1 < dist[nr][nc]) {
                        dist[nr][nc] = cd + 1;
                        queue.add(new int[]{nr, nc});
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // HEURISTIC
    // ------------------------------------------------------------------

    /**
     * A* heuristic h(n) for a given box configuration.
     * <p>
     * Must never overestimate the true number of pushes remaining (admissibility), so it
     * simply delegates to {@link #assignmentLowerBound(List)}.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return an admissible lower bound on the number of pushes needed to solve the puzzle
     *         from this configuration
     */
    private int heuristic(List<int[]> boxes) {
        // NOTE: a previous revision added a hardcoded left/right "bottleneck" penalty here.
        // Removed: it assumed every level has a single congestion point at width/2, which is
        // not generally true, and an inflated h(n) breaks A*'s admissibility guarantee --
        // meaning the search is no longer provably push-optimal, and combined with the
        // bestCost/closed-set pruning below, can permanently prune the true optimal path.
        // The pushDist precomputation already removes the per-node BFS cost that this penalty
        // was almost certainly compensating for; rely on that instead of an unsound heuristic.
        return assignmentLowerBound(boxes);
    }

    /**
     * Computes a lower bound on the remaining pushes by finding the cheapest way to match
     * every box to a distinct goal.
     * <p>
     * Edge costs come from the precomputed {@code pushDist} table (O(1) per lookup) rather
     * than a per-call BFS.  The assignment is solved exactly with the Hungarian algorithm
     * ({@link #hungarianMinCost(int[][], int, int)}, O(n^3)) so the bound stays admissible.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return the minimum total push cost of a perfect box-to-goal matching
     */
    private int assignmentLowerBound(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0) return 0;

        final int INF4 = Integer.MAX_VALUE / 4;
        int[][] cost = new int[n][numGoals];
        for (int i = 0; i < n; i++) {
            int br = boxes.get(i)[0], bc = boxes.get(i)[1];
            for (int g = 0; g < numGoals; g++) {
                int d = pushDist[g][br][bc];
                cost[i][g] = (d == Integer.MAX_VALUE) ? INF4 : d;
            }
        }

        return hungarianMinCost(cost, n, numGoals);
    }

    /**
     * Solves the minimum-cost perfect bipartite matching problem using the classic O(n^3)
     * Hungarian algorithm (Jonker-Volgenant / Kuhn-Munkres potentials version).
     * <p>
     * Supports a rectangular cost matrix ({@code n} boxes &lt;= {@code m} goals) by internally
     * padding to a square matrix with free dummy assignments.
     *
     * @param cost {@code n x m} matrix where {@code cost[i][j]} is the push cost of assigning
     *             box {@code i} to goal {@code j}
     * @param n    number of boxes (rows used in {@code cost})
     * @param m    number of goals (columns used in {@code cost})
     * @return the minimum total cost of a perfect matching of all {@code n} boxes to distinct goals
     */
    private int hungarianMinCost(int[][] cost, int n, int m) {
        // pad to a square matrix so the standard algorithm applies cleanly
        int size = Math.max(n, m);
        final int INF = Integer.MAX_VALUE / 4;
        int[][] a = new int[size + 1][size + 1];
        for (int i = 1; i <= size; i++) {
            for (int j = 1; j <= size; j++) {
                if (i <= n && j <= m) {
                    a[i][j] = cost[i - 1][j - 1];
                } else {
                    a[i][j] = 0; // padding rows/cols are free dummy assignments
                }
            }
        }

        int[] u = new int[size + 1];
        int[] v = new int[size + 1];
        int[] p = new int[size + 1]; // p[j] = row currently matched to column j
        int[] way = new int[size + 1];

        for (int i = 1; i <= size; i++) {
            p[0] = i;
            int j0 = 0;
            int[] minv = new int[size + 1];
            boolean[] used = new boolean[size + 1];
            Arrays.fill(minv, INF);

            do {
                used[j0] = true;
                int i0 = p[j0];
                int delta = INF;
                int j1 = -1;

                for (int j = 1; j <= size; j++) {
                    if (!used[j]) {
                        int cur = a[i0][j] - u[i0] - v[j];
                        if (cur < minv[j]) {
                            minv[j] = cur;
                            way[j] = j0;
                        }
                        if (minv[j] < delta) {
                            delta = minv[j];
                            j1 = j;
                        }
                    }
                }

                for (int j = 0; j <= size; j++) {
                    if (used[j]) {
                        u[p[j]] += delta;
                        v[j] -= delta;
                    } else {
                        minv[j] -= delta;
                    }
                }

                j0 = j1;
            } while (p[j0] != 0);

            do {
                int j1 = way[j0];
                p[j0] = p[j1];
                j0 = j1;
            } while (j0 != 0);
        }

        int total = 0;
        for (int j = 1; j <= size; j++) {
            if (p[j] != 0 && p[j] <= n && j <= m) {
                total += a[p[j]][j];
            }
        }
        return total;
    }

    /**
     * Determines whether the given box configuration is a deadlock — a dead end the search
     * should prune.
     * <p>
     * A state is considered deadlocked if either:
     * <ol>
     *   <li>some box that is not already on a goal is permanently frozen
     *       (see {@link #isFrozen(int, int, boolean[][], boolean[][])}), or</li>
     *   <li>no perfect matching of boxes to goals exists anymore (assignment infeasible,
     *       see {@link #hasGoalAssignment(List)}), which can happen even with no single frozen
     *       box — e.g. two boxes mutually boxed into a region that only has one reachable
     *       goal between them.</li>
     * </ol>
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return {@code true} if this configuration can never lead to a solved state
     */
    private boolean isDeadlocked(List<int[]> boxes) {
        boolean[][] boxGrid = new boolean[height][width];
        for (int[] box : boxes) {
            boxGrid[box[0]][box[1]] = true;
        }

        boolean[][] frozen = new boolean[height][width];

        for (int[] box : boxes) {
            int r = box[0];
            int c = box[1];
            if (isFrozen(r, c, boxGrid, frozen)) {
                frozen[r][c] = true;
                if (!goals[r][c]) {
                    return true; // frozen off-goal box -> puzzle can never be solved from here
                }
            }
        }

        return !hasGoalAssignment(boxes);
    }

    /**
     * Checks whether the box at {@code (r, c)} is frozen — permanently immobile.
     * <p>
     * A box is frozen if it cannot be pushed in either direction along the horizontal axis
     * AND cannot be pushed in either direction along the vertical axis (see
     * {@link #isBlockedOnAxis(int, int, int, boolean[][], boolean[][])}). A box frozen on
     * both axes can never move again, so unless it's sitting on a goal already, the state is dead.
     *
     * @param r       row of the box being checked
     * @param c       column of the box being checked
     * @param boxGrid {@code height x width} grid marking which cells currently hold a box
     * @param frozen  {@code height x width} grid marking which boxes have already been
     *                confirmed frozen earlier in the current deadlock-detection pass
     * @return {@code true} if the box can never be pushed again
     */
    private boolean isFrozen(int r, int c, boolean[][] boxGrid, boolean[][] frozen) {
        boolean blockedHorizontal = isBlockedOnAxis(r, c, 0, boxGrid, frozen);
        boolean blockedVertical   = isBlockedOnAxis(r, c, 1, boxGrid, frozen);
        return blockedHorizontal && blockedVertical;
    }

    /**
     * Checks whether the box at {@code (r, c)} is blocked along a given axis — i.e. whether
     * BOTH push directions along that axis are individually impossible.
     * <p>
     * Pushing toward side A requires: side A is a legal box destination (not a
     * wall/box/off-grid/dead-square), AND side B (the opposite side, where the player must
     * stand to perform the push) is merely walkable (not a wall/box/off-grid — dead-square
     * status doesn't matter for a player standing spot, only for where a box can land).
     *
     * @param r       row of the box being checked
     * @param c       column of the box being checked
     * @param axis    {@code 0} for horizontal (left/right), {@code 1} for vertical (up/down)
     * @param boxGrid {@code height x width} grid marking which cells currently hold a box
     * @param frozen  {@code height x width} grid marking which boxes have already been
     *                confirmed frozen earlier in the current deadlock-detection pass
     * @return {@code true} if the box cannot be pushed in either direction along this axis
     */
    private boolean isBlockedOnAxis(int r, int c, int axis, boolean[][] boxGrid, boolean[][] frozen) {
        int dRow1 = (axis == 1) ? -1 : 0;
        int dCol1 = (axis == 0) ? -1 : 0;
        int dRow2 = -dRow1;
        int dCol2 = -dCol1;

        // push toward side 1 needs: side 1 is a valid box destination, side 2 is walkable for the player
        boolean canPushToSide1 = !isBlockedSide(r, c, dRow1, dCol1, boxGrid, frozen, true)
                && !isBlockedSide(r, c, dRow2, dCol2, boxGrid, frozen, false);

        // push toward side 2 needs: side 2 is a valid box destination, side 1 is walkable for the player
        boolean canPushToSide2 = !isBlockedSide(r, c, dRow2, dCol2, boxGrid, frozen, true)
                && !isBlockedSide(r, c, dRow1, dCol1, boxGrid, frozen, false);

        return !canPushToSide1 && !canPushToSide2;
    }

    /**
     * Checks whether the neighboring cell at {@code (r+dRow, c+dCol)} blocks the box at
     * {@code (r, c)} on this side.
     * <p>
     * The neighboring cell plays one of two different roles depending on which push direction
     * is being tested, so the check differs accordingly:
     * <ul>
     *   <li>{@code asDestination == true}: can the box ever come to rest here? Blocked if it's
     *       off-grid, a wall, a dead square (landing there is an unrecoverable mistake), or
     *       another box that is itself already confirmed frozen.</li>
     *   <li>{@code asDestination == false}: can the player merely stand here to perform the
     *       push? Blocked if it's off-grid, a wall, or another box that is itself already
     *       confirmed frozen. Dead-square status is irrelevant here, since the player is never
     *       restricted from walking onto a dead square, only a box is.</li>
     * </ul>
     * In both roles, a neighboring box only blocks if that box is itself confirmed frozen
     * (mutual/chain freeze — recursion is safe since {@code frozen} only contains boxes
     * confirmed frozen earlier in this pass, so there's no cycle: a box can't be marked frozen
     * based on itself). A movable neighboring box does NOT permanently block either role, since
     * it could in principle be pushed out of the way first — whether it's sitting where this
     * box needs to land, or where the player needs to stand to push it.
     *
     * @param r             row of the box being checked
     * @param c             column of the box being checked
     * @param dRow          row offset of the side being checked ({@code -1}, {@code 0}, or {@code 1})
     * @param dCol          column offset of the side being checked ({@code -1}, {@code 0}, or {@code 1})
     * @param boxGrid       {@code height x width} grid marking which cells currently hold a box
     * @param frozen        {@code height x width} grid marking which boxes have already been
     *                      confirmed frozen earlier in the current deadlock-detection pass
     * @param asDestination {@code true} to check this side as a push destination for the box,
     *                      {@code false} to check it as a standing spot for the player
     * @return {@code true} if this side blocks the corresponding push
     */
    private boolean isBlockedSide(int r, int c, int dRow, int dCol, boolean[][] boxGrid, boolean[][] frozen, boolean asDestination) {
        int sideR = r + dRow;
        int sideC = c + dCol;

        if (sideR < 0 || sideR >= height || sideC < 0 || sideC >= width) {
            return true; // off-grid, neither a box nor the player can occupy this side
        }
        if (walls[sideR][sideC]) {
            return true;
        }
        if (asDestination && deadSquares[sideR][sideC]) {
            return true; // only relevant when checking whether a box could land here
        }
        if (boxGrid[sideR][sideC]) {
            return frozen[sideR][sideC];
        }
        return false;
    }

    /**
     * Hall's-theorem style feasibility check for box-to-goal assignment.
     * <p>
     * Determines whether a perfect matching exists that assigns every box to a distinct goal
     * it can actually reach (ignoring other boxes, since they can in principle be pushed out
     * of the way). Uses the precomputed {@code pushDist} table for O(1) reachability checks
     * instead of per-call BFS.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return {@code true} if every box can be matched to a distinct reachable goal
     */
    private boolean hasGoalAssignment(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0)         return true;
        if (numGoals < n)   return false;

        // Build adjacency using the precomputed table: box i reaches goal g iff
        // pushDist[g][br][bc] < MAX_VALUE (there exists a geometric push path to it).
        List<List<Integer>> adjacency = new ArrayList<>();
        for (int[] box : boxes) {
            int br = box[0], bc = box[1];
            List<Integer> reachableGoals = new ArrayList<>();
            for (int g = 0; g < numGoals; g++)
                if (pushDist[g][br][bc] != Integer.MAX_VALUE)
                    reachableGoals.add(g);
            adjacency.add(reachableGoals);
        }

        // Kuhn's algorithm: standard augmenting-path bipartite matching
        int[] matchGoalToBox = new int[numGoals];
        Arrays.fill(matchGoalToBox, -1);

        int matched = 0;
        for (int i = 0; i < n; i++) {
            boolean[] visited = new boolean[numGoals];
            if (tryAugment(i, adjacency, visited, matchGoalToBox)) {
                matched++;
            }
        }

        return matched == n;
    }

    /**
     * Attempts to find an augmenting path starting at the given box, as part of Kuhn's
     * bipartite matching algorithm.
     * <p>
     * Tries each goal the box can reach; if that goal is already taken, recursively attempts
     * to bump the box currently holding it to a different goal.
     *
     * @param boxIndex      index of the box (into {@code adjacency}) to find a match for
     * @param adjacency     for each box index, the list of goal indices it can reach
     * @param visited       goals already visited in the current augmenting-path search,
     *                      to avoid revisiting
     * @param matchGoalToBox current matching: {@code matchGoalToBox[j]} is the box index
     *                      matched to goal {@code j}, or {@code -1} if unmatched
     * @return {@code true} if an augmenting path was found and the matching was updated
     */
    private boolean tryAugment(int boxIndex, List<List<Integer>> adjacency, boolean[] visited, int[] matchGoalToBox) {
        for (int goalIndex : adjacency.get(boxIndex)) {
            if (visited[goalIndex]) {
                continue;
            }
            visited[goalIndex] = true;

            if (matchGoalToBox[goalIndex] == -1 || tryAugment(matchGoalToBox[goalIndex], adjacency, visited, matchGoalToBox)) {
                matchGoalToBox[goalIndex] = boxIndex;
                return true;
            }
        }
        return false;
    }

    /**
     * Terminal check for the search: is every box currently resting on a goal tile?
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return {@code true} if the puzzle is solved
     */
    private boolean isSolved(List<int[]> boxes) {
        for (int[] box : boxes) {
            if (!goals[box[0]][box[1]]) {
                return false;
            }
        }
        return true;
    }

    /**
     * ===========================================================================================
     * PART 4: A* SEARCH ENGINE AND SOLUTION RECONSTRUCTION
     * - Node (class): one A* search node -- a State plus its g/h/totalMoves/parent/move-string
     *   bookkeeping, compared lexicographically (pushes first, then total moves) by the open list
     * - stateToBoxList(): unpacks a State's sorted int[][] back into a List<int[]> for reuse
     *   with the Part 1-3 helpers that expect that shape
     * - expand(): state expansion + push generation -- the successor function for A*, tries
     *   pushing every box in every direction and enqueues the legal, non-deadlocked results
     * - buildPath(): solution reconstruction -- walks parent pointers back to the root and
     *   re-emits each edge's moves in forward order
     * - packCost(): packs a (pushes, totalMoves) pair into one long for cheap lexicographic
     *   comparison in the open-list dedup map
     * ============================================================================================
     */

    /**
     * One node in the A* search tree.
     * <p>
     * {@code state} carries the box layout plus the player's <em>canonical</em> reachable-region
     * cell, used purely for hashing/deduplication (see {@link State}). {@code trueR}/{@code trueC}
     * carry the player's actual physical position at this node -- i.e. the cell the previously
     * pushed box used to occupy, or the puzzle's literal starting cell for the root node.
     * <p>
     * Keeping these separate matters: two states with the same boxes and the same reachable
     * region are the same search state regardless of exactly where in that region the player
     * is standing (they can walk anywhere in it for free), so canonicalization is correct and
     * necessary to keep the state space from exploding. But the canonical cell is just an
     * arbitrary representative of the region (the top-left-most free cell) -- it is generally
     * NOT where the player is actually standing. Reconstructing a real, physically walkable
     * move string requires walking from the actual previous position, so {@link #expand} must
     * use {@code trueR}/{@code trueC} (never the canonical cell) as the BFS source when it
     * calls {@link #pathTo(List, int, int, int, int)}.
     * <p>
     * {@code g} and {@code totalMoves} together form the lexicographic search cost: {@code g}
     * (pushes) is the primary criterion the heuristic actually bounds, while {@code totalMoves}
     * (every real keypress, walking included) is a secondary tie-break so that among multiple
     * push-count-tied routes to the same goal, the one needing less walking is preferred.
     */
    private static class Node {
        final State state;
        final int trueR;
        final int trueC;
        final int g; // pushes made so far
        final int totalMoves; // real keypresses so far (pushes + all walking steps)
        final int h; // admissible lower bound on pushes remaining
        final Node parent;
        final String moves; // walk + push letters taken from parent to reach this node

        Node(State state, int trueR, int trueC, int g, int totalMoves, int h, Node parent, String moves) {
            this.state = state;
            this.trueR = trueR;
            this.trueC = trueC;
            this.g = g;
            this.totalMoves = totalMoves;
            this.h = h;
            this.parent = parent;
            this.moves = moves;
        }
    }

    /**
     * Unpacks a {@link State}'s sorted {@code int[][]} box array back into a {@code List<int[]>},
     * the shape every Part 1-3 helper ({@link #heuristic}, {@link #isDeadlocked}, {@link #occupied},
     * etc.) expects.
     *
     * @param state the state to unpack
     * @return the same box positions as a list, in whatever order {@link State} sorted them in
     */
    private List<int[]> stateToBoxList(State state) {
        List<int[]> list = new ArrayList<>(state.boxes.length);
        for (int[] box : state.boxes) {
            list.add(new int[]{box[0], box[1]});
        }
        return list;
    }

    /**
     * State expansion: generates every legal successor of {@code current} by trying to push
     * each box one step in each of the four directions, and enqueues the survivors onto the
     * open list.
     * <p>
     * A push of box {@code (br, bc)} in direction {@code (dRow, dCol)} requires:
     * <ol>
     *   <li>the player can actually reach the cell behind the box, {@code (br - dRow, bc - dCol)},
     *       without pushing anything else first -- checked against the box's current reachable
     *       region ({@link #findReachable});</li>
     *   <li>the destination cell, {@code (br + dRow, bc + dCol)}, is in bounds, not a wall, not
     *       a known dead square, and not already occupied by another box;</li>
     *   <li>the resulting box configuration is not an immediate deadlock -- checked last since
     *       it's the most expensive test ({@link #isDeadlocked}).</li>
     * </ol>
     * Successors that pass all three are only enqueued if they reach their resulting state at a
     * strictly better (pushes, totalMoves) lexicographic cost than any previously recorded route
     * to that same state (or are reaching it for the first time) -- this is the standard "lazy
     * deletion" pattern for using a {@link PriorityQueue} (which has no decrease-key) as an A*
     * open list, extended to a lexicographic cost so that among multiple routes tied on push
     * count, the one needing less walking wins.
     *
     * @param current   the node being expanded
     * @param boxes     {@code current}'s box positions, already unpacked via {@link #stateToBoxList}
     * @param open      the A* open list
     * @param bestCost  best known (pushes, totalMoves) lexicographic cost seen so far for each
     *                  visited state, packed via {@link #packCost}
     * @param closed    states that have already been popped and fully expanded
     */
    private void expand(Node current, List<int[]> boxes, PriorityQueue<Node> open,
                        HashMap<State, Long> bestCost, HashSet<State> closed) {

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};
        char[] dirChar = {'u', 'd', 'l', 'r'};

        // BFS 1: reachable region + canonical cell, starting from the true player position.
        // Also builds the parent map so we can reconstruct walk paths without a second BFS.
        boolean[][] reachable   = new boolean[height][width];
        int[][] walkParentR     = new int[height][width];
        int[][] walkParentC     = new int[height][width];
        int[] canonical         = {current.trueR, current.trueC};

        reachable[current.trueR][current.trueC] = true;
        Queue<int[]> bfsQueue = new LinkedList<>();
        bfsQueue.add(new int[]{current.trueR, current.trueC});

        while (!bfsQueue.isEmpty()) {
            int[] cur = bfsQueue.poll();
            int cr = cur[0], cc = cur[1];

            for (int i = 0; i < 4; i++) {
                int nr = cr + dRow[i], nc = cc + dCol[i];
                if (occupied(boxes, nr, nc) || reachable[nr][nc]) continue;
                reachable[nr][nc] = true;
                walkParentR[nr][nc] = cr;
                walkParentC[nr][nc] = cc;
                bfsQueue.add(new int[]{nr, nc});
                if (nr < canonical[0] || (nr == canonical[0] && nc < canonical[1])) {
                    canonical[0] = nr;
                    canonical[1] = nc;
                }
            }
        }

        for (int boxIndex = 0; boxIndex < boxes.size(); boxIndex++) {
            int[] box = boxes.get(boxIndex);
            int br = box[0], bc = box[1];

            for (int dir = 0; dir < 4; dir++) {
                int standR = br - dRow[dir];
                int standC = bc - dCol[dir];
                int destR  = br + dRow[dir];
                int destC  = bc + dCol[dir];

                if (standR < 0 || standR >= height || standC < 0 || standC >= width) continue;
                if (!reachable[standR][standC]) continue;
                if (destR < 0 || destR >= height || destC < 0 || destC >= width) continue;
                if (walls[destR][destC] || deadSquares[destR][destC]) continue;
                if (occupied(boxes, destR, destC)) continue;

                List<int[]> newBoxes = new ArrayList<>(boxes.size());
                for (int[] b : boxes) newBoxes.add(b);
                newBoxes.set(boxIndex, new int[]{destR, destC});

                if (isDeadlocked(newBoxes)) continue;

                // BFS 2: reachable region from the box's old position in the NEW box layout,
                // to find the canonical cell. No pathTo() call needed — we already have the
                // walk parent map from BFS 1 above.
                boolean[][] newReachable = new boolean[height][width];
                int[] newCanonical = {br, bc};
                newReachable[br][bc] = true;
                Queue<int[]> canonQueue = new LinkedList<>();
                canonQueue.add(new int[]{br, bc});

                while (!canonQueue.isEmpty()) {
                    int[] cur = canonQueue.poll();
                    int cr = cur[0], cc = cur[1];
                    for (int i = 0; i < 4; i++) {
                        int nr = cr + dRow[i], nc = cc + dCol[i];
                        if (nr < 0 || nr >= height || nc < 0 || nc >= width) continue;
                        if (walls[nr][nc] || newReachable[nr][nc]) continue;
                        boolean blockedByBox = false;
                        for (int[] b : newBoxes) if (b[0] == nr && b[1] == nc) { blockedByBox = true; break; }
                        if (blockedByBox) continue;
                        newReachable[nr][nc] = true;
                        canonQueue.add(new int[]{nr, nc});
                        if (nr < newCanonical[0] || (nr == newCanonical[0] && nc < newCanonical[1])) {
                            newCanonical[0] = nr;
                            newCanonical[1] = nc;
                        }
                    }
                }

                State newState = new State(newBoxes, newCanonical[0], newCanonical[1]);
                if (closed.contains(newState)) continue;

                // Reconstruct walk path using the parent map from BFS 1 — O(path length) only,
                // no additional BFS.
                StringBuilder walkSB = new StringBuilder();
                int cr = standR, cc = standC;
                while (cr != current.trueR || cc != current.trueC) {
                    int pr = walkParentR[cr][cc], pc = walkParentC[cr][cc];
                    walkSB.append(stepChar(pr, pc, cr, cc));
                    cr = pr; cc = pc;
                }
                String walk  = walkSB.reverse().toString();
                String moves = walk + dirChar[dir];

                int  g2          = current.g + 1;
                int  totalMoves2 = current.totalMoves + moves.length();
                long newCost     = packCost(g2, totalMoves2);
                Long prevBest    = bestCost.get(newState);
                if (prevBest != null && prevBest <= newCost) continue;
                bestCost.put(newState, newCost);

                int h2 = heuristic(newBoxes);
                open.add(new Node(newState, br, bc, g2, totalMoves2, h2, current, moves));
            }
        }
    }

    /**
     * Solution reconstruction: walks the parent chain from the goal node back to the root,
     * collecting each edge's move string, then re-emits them in forward (root-to-goal) order.
     *
     * @param goalNode the node whose box configuration satisfies {@link #isSolved}
     * @return the full move string -- every {@code u}/{@code d}/{@code l}/{@code r} from the
     *         puzzle's start to the solved configuration, in order
     */
    private String buildPath(Node goalNode) {
        ArrayDeque<String> segments = new ArrayDeque<>();
        Node cur = goalNode;
        while (cur.parent != null) {
            segments.addFirst(cur.moves);
            cur = cur.parent;
        }

        StringBuilder solution = new StringBuilder();
        for (String segment : segments) {
            solution.append(segment);
        }
        return solution.toString();
    }

    /**
     * Packs a (pushes, totalMoves) pair into a single {@code long} so two lexicographic costs
     * can be compared with one numeric comparison. Safe as long as {@code totalMoves} stays
     * under 1,000,000, which the time/node budget in {@link #solveSokobanPuzzle} guarantees.
     *
     * @param pushes     number of pushes in this cost
     * @param totalMoves number of real keypresses (pushes + walking) in this cost
     * @return a single comparable long encoding both, pushes as the more significant component
     */
    private static long packCost(int pushes, int totalMoves) {
        return (long) pushes * 1_000_000L + totalMoves;
    }
}
