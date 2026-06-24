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
        final int MAX_NODES = 400_000;
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
     * ============================================================================================
     */

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
        return assignmentLowerBound(boxes);
    }

    /**
     * Computes a lower bound on the remaining pushes by finding the cheapest way to match
     * every box to a distinct goal.
     * <p>
     * Edge costs are box-to-goal push distances obtained via {@link #bfsPushDistanceFromBox(int, int)}.
     * The assignment is solved exactly with the Hungarian algorithm ({@link #hungarianMinCost(int[][], int, int)},
     * O(n^3)) so the bound stays admissible — a greedy nearest-goal match is NOT admissible and
     * can make A* return suboptimal plans.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return the minimum total push cost of a perfect box-to-goal matching
     */
    private int assignmentLowerBound(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0) {
            return 0;
        }

        List<int[]> goalList = new java.util.ArrayList<>();
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (goals[r][c]) {
                    goalList.add(new int[]{r, c});
                }
            }
        }

        int m = goalList.size();
        // cost[i][j] = pushes needed to get box i onto goal j (box-to-cell distance via distanceTable,
        // since distanceTable[r][c] already holds the shortest goal-distance computed backwards from
        // every goal; here we instead need box-i-specific distances, so fall back to BFS per box
        // when more than one goal/box is involved would be too slow to repeat from scratch, so we
        // reuse distanceTable only as a fast per-cell estimate when n == 1, and do exact per-box BFS otherwise).
        int[][] cost = new int[n][m];
        for (int i = 0; i < n; i++) {
            int[] boxPos = boxes.get(i);
            int[][] distFromBox = bfsPushDistanceFromBox(boxPos[0], boxPos[1]);
            for (int j = 0; j < m; j++) {
                int gr = goalList.get(j)[0];
                int gc = goalList.get(j)[1];
                int d = distFromBox[gr][gc];
                cost[i][j] = (d == Integer.MAX_VALUE) ? Integer.MAX_VALUE / 4 : d;
            }
        }

        return hungarianMinCost(cost, n, m);
    }

    /**
     * Computes single-box push distances via BFS over box positions only.
     * <p>
     * This ignores whether the player can actually reach the push side on the other end of
     * each move — it purely measures the minimum number of pushes to slide one box from
     * {@code (startR, startC)} to every other reachable cell, treating walls as blocking.
     * Used to build assignment cost rows for {@link #assignmentLowerBound(List)} and reachable-goal
     * adjacency for {@link #hasGoalAssignment(List)}.
     *
     * @param startR starting row of the box
     * @param startC starting column of the box
     * @return a {@code height x width} grid where each cell holds the minimum push distance
     *         from the start position, or {@link Integer#MAX_VALUE} if unreachable
     */
    private int[][] bfsPushDistanceFromBox(int startR, int startC) {
        int[][] dist = new int[height][width];
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                dist[r][c] = Integer.MAX_VALUE;
            }
        }

        dist[startR][startC] = 0;
        Queue<int[]> queue = new LinkedList<>();
        queue.add(new int[]{startR, startC});

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};

        while (!queue.isEmpty()) {
            int[] current = queue.poll();
            int currRow = current[0];
            int currCol = current[1];
            int currentDist = dist[currRow][currCol];

            for (int i = 0; i < 4; i++) {
                int nextRow = currRow + dRow[i];
                int nextCol = currCol + dCol[i];

                if (nextRow < 0 || nextRow >= height || nextCol < 0 || nextCol >= width) {
                    continue;
                }
                if (walls[nextRow][nextCol]) {
                    continue;
                }
                if (currentDist + 1 < dist[nextRow][nextCol]) {
                    dist[nextRow][nextCol] = currentDist + 1;
                    queue.add(new int[]{nextRow, nextCol});
                }
            }
        }

        return dist;
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
        boolean blockedVertical = isBlockedOnAxis(r, c, 1, boxGrid, frozen);
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
     * of the way). If no such matching exists, the puzzle is unsolvable from this state
     * regardless of any single box's mobility. Solved via Kuhn's augmenting-path bipartite
     * matching algorithm (see {@link #tryAugment(int, List, boolean[], int[])}).
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return {@code true} if every box can be matched to a distinct reachable goal
     */
    private boolean hasGoalAssignment(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0) {
            return true;
        }

        List<int[]> goalList = new java.util.ArrayList<>();
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (goals[r][c]) {
                    goalList.add(new int[]{r, c});
                }
            }
        }

        int m = goalList.size();
        if (m < n) {
            return false; // can't possibly match every box to a distinct goal
        }

        // build box -> reachable-goal adjacency (reachable meaning: connected to the box's
        // cell through non-wall tiles, i.e. there's at least a geometric path for it to be
        // pushed there with the other boxes hypothetically out of the way)
        List<List<Integer>> adjacency = new java.util.ArrayList<>();
        for (int[] box : boxes) {
            int[][] dist = bfsPushDistanceFromBox(box[0], box[1]);
            List<Integer> reachableGoals = new java.util.ArrayList<>();
            for (int j = 0; j < m; j++) {
                int gr = goalList.get(j)[0];
                int gc = goalList.get(j)[1];
                if (dist[gr][gc] != Integer.MAX_VALUE) {
                    reachableGoals.add(j);
                }
            }
            adjacency.add(reachableGoals);
        }

        // Kuhn's algorithm: standard augmenting-path bipartite matching
        int[] matchGoalToBox = new int[m];
        Arrays.fill(matchGoalToBox, -1);

        int matched = 0;
        for (int i = 0; i < n; i++) {
            boolean[] visited = new boolean[m];
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

        Reach reach = findReachable(boxes, current.trueR, current.trueC);

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};
        char[] dirChar = {'u', 'd', 'l', 'r'};

        for (int boxIndex = 0; boxIndex < boxes.size(); boxIndex++) {
            int[] box = boxes.get(boxIndex);
            int br = box[0];
            int bc = box[1];

            for (int dir = 0; dir < 4; dir++) {
                int standR = br - dRow[dir]; // where the player must stand to push this box this way
                int standC = bc - dCol[dir];
                int destR = br + dRow[dir];  // where the box would land
                int destC = bc + dCol[dir];

                if (standR < 0 || standR >= height || standC < 0 || standC >= width) {
                    continue;
                }
                if (!reach.reachable[standR][standC]) {
                    continue; // player can't get behind the box to push it this way
                }

                if (destR < 0 || destR >= height || destC < 0 || destC >= width) {
                    continue;
                }
                if (walls[destR][destC] || deadSquares[destR][destC]) {
                    continue; // illegal landing spot, or provably unsolvable from there
                }
                if (occupied(boxes, destR, destC)) {
                    continue; // another box is already sitting there
                }

                // build the successor box configuration: every box stays put except this one
                List<int[]> newBoxes = new ArrayList<>(boxes.size());
                for (int[] b : boxes) {
                    newBoxes.add(b);
                }
                newBoxes.set(boxIndex, new int[]{destR, destC});

                if (isDeadlocked(newBoxes)) {
                    continue; // frozen-box / Hall's-theorem prune
                }

                // the player physically ends up where the box used to be
                int[] canonical = canonicalPlayer(newBoxes, br, bc);
                State newState = new State(newBoxes, canonical[0], canonical[1]);

                if (closed.contains(newState)) {
                    continue;
                }

                // walk from the TRUE current position (not the canonical one) to behind the box
                String walk = pathTo(boxes, current.trueR, current.trueC, standR, standC);
                String moves = walk + dirChar[dir];

                int g2 = current.g + 1; // one push
                int totalMoves2 = current.totalMoves + moves.length(); // walk steps + this push

                long newCost = packCost(g2, totalMoves2);
                Long prevBest = bestCost.get(newState);
                if (prevBest != null && prevBest <= newCost) {
                    continue; // already reached this configuration at least as cheaply
                }
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
