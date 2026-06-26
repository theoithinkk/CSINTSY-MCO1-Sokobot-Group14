package solver;

import java.util.ArrayDeque;    // collects the solution's move segments when we rebuild the path
import java.util.ArrayList;     // general-purpose lists, mostly the box position lists
import java.util.Arrays;        // sorting and hashing the box arrays inside State
import java.util.Comparator;    // orders the nodes waiting in the open list
import java.util.HashMap;       // bestCost: cheapest known cost we've seen for each state
import java.util.HashSet;       // closed: states we've already finished expanding
import java.util.LinkedList;    // the queue type behind every BFS in here
import java.util.List;          // the box position lists we pass around (List<int[]>)
import java.util.PriorityQueue; // the A* open list itself
import java.util.Queue;         // BFS queue interface

public class SokoBot {

    // Max width of the puzzle grid
    private int width;

    //Max height of the puzzle grid
    private int height;

    //Matrix for storing the wall locations: True for Wall | False for player, box or a goal
    private boolean[][] walls;

    //Matrix for goals: True for goal present here | False for any other grid type
    private boolean[][] goals;

    //Matrix for storing dead tiles: True for making puzzle unsolveable if box goes here | False for safe
    private boolean[][] deadSquares;

    //Lookup table for push distance | One will exist per goal. Format of matrix is pushDist[g][r][c]
    //g indicating goal
    //r and c indicating fewest pushes to move box onto goal
    private int[][][] pushDist;

    //Maps each goal index to its board coordinates {row, col}.
    //Used solely to seed the per-goal BFS in computeAllPushDistances()
    private int[][] goalPos;

    //How many goals the puzzle has
    private int numGoals;

    // Heuristic weight for weighted A*. Values above 1 trade push-optimality for speed.
    private static final int H_WEIGHT = 2;


    /**
     * Runs the whole solve. It reads where the player and boxes start, then searches through
     * possible box arrangements with A* until it lands on one where every box is on a goal,
     * or until it runs out of time.
     *
     * Every node tracks two numbers: how many pushes it took to get there, and how many total
     * keypresses (pushes plus all the walking in between). Pushes are what the search mainly
     * cares about; total keypresses are only a tie-breaker, so when two routes need the same
     * number of pushes, the one with less walking wins.
     *
     * Note the search is weighted, so it favors speed over finding the absolute shortest push
     * count. It returns a solution that works and fits the time budget, not necessarily the
     * shortest one.
     *
     * @param width     width of the puzzle grid
     * @param height    height of the puzzle grid
     * @param mapData   the static layout, '#' for walls and '.' for goals
     * @param itemsData the movable stuff, '@' for the player and '$' for boxes
     * @return a string of u/d/l/r moves that solves the puzzle, or an empty string if nothing was found in time
     */
    public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {

        //Time budget for the bot to think of a solution
        long deadline = System.nanoTime() + 15_000_000_000L;

        initialize(width, height, mapData, itemsData);

        //For parsing dynamic items like the player's start loc and where every box is
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

        //Unsolvable from the start position
        if (isDeadlocked(boxes)) {
            return "";
        }

        // --- A* bookkeeping ---
        // The open list is ordered by g + H_WEIGHT*h, with totalMoves as a tie-breaker
        // so that among equally ranked nodes, the one with less walking comes out first.
        int[] canonicalStart = canonicalPlayer(boxes, startPlayerR, startPlayerC);
        State startState = new State(boxes, canonicalStart[0], canonicalStart[1]);

        PriorityQueue<Node> open = new PriorityQueue<>(
                Comparator.<Node>comparingInt(n -> n.g + H_WEIGHT * n.h)
                        .thenComparingInt(n -> n.h)
                        .thenComparingInt(n -> n.totalMoves)
        );

        //bestCost stores the best (pushes, totalMoves) cost seen so far for each state,
        //All paacked into a single long for easy comparison.
        HashMap<State, Long> bestCost = new HashMap<>();
        HashSet<State> closed = new HashSet<>();

        Node startNode = new Node(startState, startPlayerR, startPlayerC, 0, 0, heuristic(boxes), null, "");
        open.add(startNode);
        bestCost.put(startState, packCost(0, 0));

        //Keep pulling the lowest-cost node until the puzzle is solved or time runs out
        while (!open.isEmpty()) {

            if (System.nanoTime() > deadline) {
                return "";
            }

            Node current = open.poll();

            if (closed.contains(current.state)) {
                continue;
            }
            closed.add(current.state);

            List<int[]> currentBoxes = stateToBoxList(current.state);

            if (isSolved(currentBoxes)) {
                return buildPath(current);
            }

            expand(current, currentBoxes, open, bestCost, closed);
        }

        return ""; //No solution found
    }

    /**
     * ===========================================================================================
     * PART 1: BOARD REPRESENTATION AND PREPROCESSING
     * - initialize(): reads the raw map into the wall/goal grids, then kicks off the prep below
     * - computeDeadSquares(): marks non-goal cells a box can never escape from (corners and dead
     *   corridors), so the search can refuse to push a box there in the first place
     * - computeAllPushDistances(): builds the per-goal push-distance tables the heuristic relies on
     * - computeBoxGoalDistances(): older nearest-goal distance table, currently unused (see its doc)
     * ============================================================================================
     */

    /**
     * Sets up the board before the search starts.
     * Reads the raw map and marks which cells are walls and which are goals into their own
     * grids. Then runs two preprocessing steps the search relies on later: dead square detection
     * (cells to never push a box onto) and the push distance tables the heuristic reads from.
     *
     * @param width     the width of the puzzle board
     * @param height    the height of the puzzle board
     * @param mapData   the static layout: walls and goals
     * @param itemsData the movable layout: the player and the boxes
     */
    private void initialize(int width, int height, char[][] mapData, char[][] itemsData) {

        this.width = width;
        this.height = height;

        //Instantiate the walls and goals matrices based on the map data
        this.walls = new boolean[height][width];
        this.goals = new boolean[height][width];

        //Main loop for puzzle board parsing
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                char staticTile = mapData[r][c];

                //Wall detection (set walls[r][c] to true if there is a wall at (r, c))
                if (staticTile == '#') {
                    this.walls[r][c] = true;
                }
                //Goal detection (set goals[r][c] to true if there is a goal at (r, c))
                else if (staticTile == '.') {
                    this.goals[r][c] = true;
                }
            }
        }

        computeDeadSquares();      //Find cells a box could get permanently stuck on
        computeAllPushDistances(); //Build the per-goal push-distance tables the heuristic uses
    }

    /**
     * Classifies which tiles are dead squares on the Sokoban board and marks them in a 2D matrix.
     *
     * A dead square is any non-goal tile where pushing a box onto it makes the puzzle unsolvable.
     * Marking these during preprocessing lets the solver avoid moves that inevitably lead to a dead end.
     *
     * Two cases are detected: dead corners, which are non-goal tiles adjacent to walls on two
     * perpendicular sides, and dead corridors, which are sequences of non-goal tiles between two
     * dead corners that run along a continuous wall and contain no goals.
     *
     * Results are stored in the deadSquares matrix, where true means the solver should never
     * push a box onto that tile.
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

                //Mark the tile as a dead square if it is a corner
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
                //start only if it is already marked as a dead square and is not a goal
                if (!deadSquares[r][c] || goals[r][c]) {
                    continue;
                }
                //Scan to the right
                int column = c + 1;
                boolean goalDetected = false;
                //Traverse until a wall is reached and if goal has been detected, do not mark the corridor as a dead corridor
                while (column < width && !walls[r][column]) {
                    if (goals[r][column]) {
                        goalDetected = true;
                        break;
                    }

                    if (deadSquares[r][column]) {
                        boolean wallNorth = true;
                        boolean wallSouth = true;
                        //Corridor is only valid if atleast one side of the corridor is a continuous wall (for it to be completely dead)
                        for (int check = c; check <= column; check++) {
                            //Check if wall above is broken
                            if (r - 1 < 0 || !walls[r - 1][check]) {
                                wallNorth = false;
                            }
                            //Check if wall below is broken
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
                //Start only if it is already marked as a dead square and is not a goal
                if (!deadSquares[r][c] || goals[r][c]) {
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
                            //Check if left wall is continuous
                            if (c - 1 < 0 || !walls[check][c - 1]) {
                                wallWest = false;
                            }
                            //Check if right wall is continuous
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
     * ===========================================================================================
     * PART 2: PLAYER MOVEMENT AND STATE REPRESENTATION
     * - occupied(): quick check if a cell is blocked for the player (wall or box)
     * - findReachable(): BFS that checks every cell the player can walk to without pushing a box
     * - canonicalPlayer(): collapses the player's whole reachable region down to one cell
     * - Reach (class): the result of findReachable (reachable grid + canonical cell)
     * - State (class): one search node (box layout + canonical player) with equals/hashCode
     * ============================================================================================
     */

    /**
     * Checks whether the player is blocked from standing on a cell. A cell counts as blocked if
     * it's off the grid, a wall, or has a box sitting on it. Goals don't block anyone, so the
     * player can freely walk over an empty goal.
     *
     * @param boxes the current box positions
     * @param r     row to check
     * @param c     column to check
     * @return true if the player can't be on that cell
     */
    private boolean occupied(List<int[]> boxes, int r, int c) {
        if (r < 0 || r >= height || c < 0 || c >= width) {
            return true; //Off-grid counts as blocked so no need to bounds-check everywhere else
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
     * Floods outward from the player to find every cell they can walk to without pushing any box,
     * using a plain BFS. Along the way it also tracks the canonical cell for that whole region:
     * the top-left-most reachable cell, scanning by row then column.
     *
     * Why the canonical cell matters: as long as the boxes don't move, it doesn't matter exactly
     * where in a region the player is standing, since they can reach any of it for free. Collapsing
     * the whole region to one fixed cell lets two otherwise-identical board states count as the
     * same state, which keeps the search from exploring the same thing over and over.
     *
     * @param boxes   the current box positions
     * @param playerR the player's row
     * @param playerC the player's column
     * @return a Reach holding the reachable-cell grid and that region's canonical cell
     */
    private Reach findReachable(List<int[]> boxes, int playerR, int playerC) {
        boolean[][] reachable = new boolean[height][width];
        Queue<int[]> queue = new LinkedList<>();

        reachable[playerR][playerC] = true;
        queue.add(new int[]{playerR, playerC});

        //Canonical = top left most cell in the whole region. start it at the player, then update it.
        int[] canonical = new int[]{playerR, playerC};

        int[] dRow = {-1, 1, 0, 0};
        int[] dCol = {0, 0, -1, 1};
        //Loops until the whole region is checked
        while (!queue.isEmpty()) {
            int[] current = queue.poll();
            int currRow = current[0];
            int currCol = current[1];
            //Check the current tile's neighbors
            for (int i = 0; i < 4; i++) {
                int nextRow = currRow + dRow[i];
                int nextCol = currCol + dCol[i];
                //Skip walls, boxes, off-grid, and already-visited tiles
                if (occupied(boxes, nextRow, nextCol) || reachable[nextRow][nextCol]) {
                    continue;
                }

                //Mark as reachable, then load to queue
                reachable[nextRow][nextCol] = true;
                queue.add(new int[]{nextRow, nextCol});

                //Update canonical if we found a cell higher up, or further left on the same row
                if (nextRow < canonical[0] || (nextRow == canonical[0] && nextCol < canonical[1])) {
                    canonical[0] = nextRow;
                    canonical[1] = nextCol;
                }
            }
        }

        return new Reach(reachable, canonical);
    }

    /**
     * Shortcut that runs findReachable and hands back just the canonical cell, for when
     * the caller only needs that one representative cell and not the full reachable grid.
     *
     * @param boxes   the current box positions
     * @param playerR the player's row
     * @param playerC the player's column
     * @return the {row, col} of the region's canonical (top-left-most) cell
     */
    private int[] canonicalPlayer(List<int[]> boxes, int playerR, int playerC) {
        return findReachable(boxes, playerR, playerC).canonical;
    }

    /**
     * Turns a single one-cell step into its move letter. Assumes from and to are
     * neighbors, so the four cases cover every possibility.
     *
     * @param fromR row stepped from
     * @param fromC column stepped from
     * @param toR   row stepped to
     * @param toC   column stepped to
     * @return u, d, l, or r
     */
    private char stepChar(int fromR, int fromC, int toR, int toC) {
        if (toR == fromR - 1) return 'u'; //Moved one row up
        if (toR == fromR + 1) return 'd'; //Moved one row down
        if (toC == fromC - 1) return 'l'; //Moved one column left
        return 'r';                       //Moved one column right
    }

    /**
     * The two things findReachable produces: a grid of where the player can walk, and the
     * one canonical cell that stands in for that whole region. Just a small bundle so the method
     * can hand back both at once.
     */
    private static class Reach {
        //Reachable[r][c] is true if the player can walk to that cell without pushing a box.
        final boolean[][] reachable;
        //The region's stand-in cell: the top-left-most reachable cell.
        final int[] canonical;

        Reach(boolean[][] reachable, int[] canonical) {
            this.reachable = reachable;
            this.canonical = canonical;
        }
    }

    /**
     * One snapshot of the puzzle the search treats as a single state: where all the boxes are, plus
     * the canonical player cell. Two States are equal when the boxes match and the player's region
     * matches, which is what lets the search recognize when it's reached the same situation again
     * and skip re-exploring it.
     *
     * The boxes get sorted on the way in so that the same set of boxes always produces the same
     * array no matter what order they came in. Without that, two identical boards could look
     * different just because their box lists were ordered differently. The hash is computed once in
     * the constructor and cached, since this gets dropped into hash maps and sets constantly.
     */
    private static class State {
        //Box coordinates, sorted by row then column so equal boards always look equal
        final int[][] boxes;
        //The canonical player row (top-left-most cell of the reachable region)
        final int playerR;
        //The canonical player column.
        final int playerC;
        //Precomputed hash, cached so hashCode() stays cheap
        private final int hash;

        State(List<int[]> boxList, int playerR, int playerC) {
            //Pull the boxes into a 2D array and sort them by row first, then column
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

        //Builds the cached hash from the sorted boxes and the player cell
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

        /**
         * Two States match when the player's canonical cell is the same and all box positions line
         * up. The boxes were sorted in the constructor, so a straight array compare is enough.
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
     * - computeAllPushDistances(): precomputes how many pushes it takes to reach each goal from any cell
     * - heuristic(): estimates how many pushes are still needed from the current box layout
     * - assignmentLowerBound(): finds the cheapest way to assign every box to a distinct goal
     * - hungarianMinCost(): solves the assignment problem using the Hungarian algorithm
     * - isDeadlocked(): checks if the current box layout can never lead to a solution
     * - isFrozen(): checks if a single box is permanently stuck
     * - isBlockedOnAxis() / isBlockedSide(): helpers for the freeze check, one axis at a time
     * - hasGoalAssignment(): checks if every box can still reach a distinct goal
     * - tryAugment(): helper for the goal assignment check
     * - isSolved(): checks if every box is on a goal
     *
     * Distances are precomputed because the heuristic and deadlock check both need to know how
     * far each box is from each goal on every state the search visits. Running a fresh BFS for
     * that each time would be very slow, so computeAllPushDistances() does it all once at startup
     * and stores the results in a table. Every distance lookup during the search is then instant.
     * ============================================================================================
     */

    /**
     * Builds a table of push distances from every cell to every goal.
     *
     * Runs one BFS per goal starting from that goal's position outward. For each cell it
     * records how many pushes a box would need to reach that goal from there. Results are
     * stored in pushDist indexed by [goal][row][col].
     *
     * This runs once at startup so the search never has to recompute distances on the fly.
     */
    private void computeAllPushDistances() {
        //Collect the (row, col) of every goal tile on the board
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
            //The goal itself costs 0 pushes — a box already there needs no moves
            int gr = goalPos[g][0], gc = goalPos[g][1];
            dist[gr][gc] = 0;

            Queue<int[]> queue = new LinkedList<>();
            queue.add(new int[]{gr, gc});
            //BFS expanding outward from the goal; each step = one more push needed
            while (!queue.isEmpty()) {
                int[] cur = queue.poll();
                int cr  = cur[0], cc = cur[1];
                int cd  = dist[cr][cc];

                for (int i = 0; i < 4; i++) {
                    int nr = cr + dRow[i], nc = cc + dCol[i];
                    if (nr < 0 || nr >= height || nc < 0 || nc >= width) continue;
                    if (walls[nr][nc]) continue; //Walls are impassable for boxes
                    // Only update if we found a cheaper route to this neighbor
                    if (cd + 1 < dist[nr][nc]) {
                        dist[nr][nc] = cd + 1;
                        queue.add(new int[]{nr, nc});
                    }
                }
            }
        }
    }

    /**
     * Estimates how many pushes are still needed from the current box layout.
     * Delegates to assignmentLowerBound, which finds the true minimum by matching
     * every box to a distinct goal as cheaply as possible.
     *
     * This estimate never overshoots the real answer, so the search stays correct.
     * The one place we trade solution quality for speed is the H_WEIGHT multiplier
     * in the open list, not here.
     *
     * @param boxes current box positions, each as {row, col}
     * @return a lower bound on the number of pushes still needed
     */
    private int heuristic(List<int[]> boxes) {
        return assignmentLowerBound(boxes);
    }

    /**
     * Finds the cheapest way to assign every box to a distinct goal and returns the total cost.
     * Uses the precomputed pushDist table so each box-to-goal cost is just a table lookup.
     * The assignment itself is solved with the Hungarian algorithm.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return the minimum total push cost of matching all boxes to distinct goals
     */
    private int assignmentLowerBound(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0) return 0;

        // INF4 instead of MAX_VALUE to prevent overflow when the Hungarian algorithm
        // does arithmetic on these costs (e.g. subtraction in the dual variable updates)
        final int INF4 = Integer.MAX_VALUE / 4;

        // Build the n x numGoals cost matrix from the precomputed push-distance table
        int[][] cost = new int[n][numGoals];
        for (int i = 0; i < n; i++) {
            int br = boxes.get(i)[0], bc = boxes.get(i)[1];
            for (int g = 0; g < numGoals; g++) {
                int d = pushDist[g][br][bc];
                cost[i][g] = (d == Integer.MAX_VALUE) ? INF4 : d; //Cap unreachable goals so they're still assignable but never preferred
            }
        }

        return hungarianMinCost(cost, n, numGoals);
    }

    /**
     * Solves the minimum-cost assignment problem using the Hungarian algorithm.
     * Finds the cheapest way to match n boxes to m goals, where each box gets
     * a distinct goal. Pads the cost matrix to square internally if n and m differ.
     *
     * @param cost n x m matrix where cost[i][j] is the push cost of sending box i to goal j
     * @param n    number of boxes
     * @param m    number of goals
     * @return the minimum total cost of a complete box-to-goal matching
     */
    private int hungarianMinCost(int[][] cost, int n, int m) {
        //Time spent trying to implement this algorithm: 17 hours
        //For anyone reading this, I documented this whole thing as in-depth as my
        //brain can handle so it is clear what type of dark magic I performed to make it work. - Schuyler
        int size = Math.max(n, m);
        final int INF = Integer.MAX_VALUE / 4;

        //1-indexed copy of the cost matrix, padded to square with free dummy assignments
        int[][] a = new int[size + 1][size + 1];
        for (int i = 1; i <= size; i++) {
            for (int j = 1; j <= size; j++) {
                a[i][j] = (i <= n && j <= m) ? cost[i - 1][j - 1] : 0;
            }
        }

        //Dual variables for rows (u) and columns (v): the algorithm keeps these as
        //"potentials" and adjusts them so that the reduced cost a[i][j]-u[i]-v[j]
        //is always >= 0. When it hits exactly 0 for a matched pair, that pair is optimal.
        int[] u = new int[size + 1];
        int[] v = new int[size + 1];

        //p[j] = which box is currently matched to goal j (0 means unmatched)
        int[] p = new int[size + 1];

        //way[j] = which goal column we came from when we found the best reduced cost to j,
        //used to retrace and flip the augmenting path at the end of each round
        int[] way = new int[size + 1];

        //Add one box at a time, extending the matching to cover it
        for (int i = 1; i <= size; i++) {
            p[0] = i; // sentinel: treat column 0 as a fake "entry point" holding the current box
            int j0 = 0;

            //minv[j] = best reduced cost seen so far to reach unmatched goal j in this round
            int[] minv = new int[size + 1];
            boolean[] used = new boolean[size + 1]; //goals already on the augmenting path
            Arrays.fill(minv, INF);

            //Walk the augmenting path: each iteration locks in one more column and
            //finds the next cheapest column to extend to
            do {
                used[j0] = true;
                int i0 = p[j0]; //box currently sitting at column j0
                int delta = INF;
                int j1 = -1;

                for (int j = 1; j <= size; j++) {
                    if (!used[j]) {
                        //Reduced cost: how much this assignment costs above the current dual values
                        int cur = a[i0][j] - u[i0] - v[j];
                        if (cur < minv[j]) {
                            minv[j] = cur;
                            way[j] = j0; //remember we reached j from j0
                        }
                        if (minv[j] < delta) {
                            delta = minv[j];
                            j1 = j; //j1 is the cheapest next column to lock in
                        }
                    }
                }

                //Shift the dual variables by delta to keep reduced costs non-negative.
                //Columns on the path get their potentials updated; others get minv reduced
                //by the same amount so relative distances stay correct for the next iteration.
                for (int j = 0; j <= size; j++) {
                    if (used[j]) {
                        u[p[j]] += delta;
                        v[j] -= delta;
                    } else {
                        minv[j] -= delta;
                    }
                }

                j0 = j1; //advance to the column we just locked in
            } while (p[j0] != 0); //stop once we reach an unmatched column

            //Flip the augmenting path to include the new box in the matching
            do {
                int j1 = way[j0];
                p[j0] = p[j1];
                j0 = j1;
            } while (j0 != 0);
        }

        //Sum up the costs for real box-to-goal pairs only, ignoring dummy padding assignments
        int total = 0;
        for (int j = 1; j <= size; j++) {
            if (p[j] != 0 && p[j] <= n && j <= m) {
                total += a[p[j]][j];
            }
        }
        return total;
    }

    /**
     * Returns true if the current box layout can never lead to a solution.
     *
     * Two things are checked: whether any box that isn't on a goal is permanently stuck
     * and can never be pushed again, and whether there's still a way to match every box
     * to a distinct reachable goal. If either check fails, the state is a dead end.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return true if this layout can never be solved
     */
    private boolean isDeadlocked(List<int[]> boxes) {
        //Grid form of box positions so isFrozen can do O(1) occupancy checks
        boolean[][] boxGrid = new boolean[height][width];
        for (int[] box : boxes) {
            boxGrid[box[0]][box[1]] = true;
        }

        //Tracks which boxes have already been confirmed stuck, so that when
        //isFrozen checks a neighbor it knows whether that neighbor can still move
        boolean[][] frozen = new boolean[height][width];

        for (int[] box : boxes) {
            int r = box[0];
            int c = box[1];
            if (isFrozen(r, c, boxGrid, frozen)) {
                frozen[r][c] = true; //Mark so neighboring boxes can factor this in
                if (!goals[r][c]) {
                    return true; //Stuck off a goal, in other words no way to fix this
                }
            }
        }

        //Even if no box is individually frozen, the layout can still be unsolvable
        //if there's no way to assign every box to a distinct reachable goal
        return !hasGoalAssignment(boxes);
    }

    /**
     * Returns true if the box at (r, c) is permanently stuck and can never be pushed again.
     * A box is stuck if it's blocked on both the horizontal and vertical axes.
     *
     * @param r       row of the box
     * @param c       column of the box
     * @param boxGrid grid marking which cells have a box
     * @param frozen  grid marking which boxes are already confirmed stuck
     * @return true if the box can never move again
     */
    private boolean isFrozen(int r, int c, boolean[][] boxGrid, boolean[][] frozen) {
        boolean blockedHorizontal = isBlockedOnAxis(r, c, 0, boxGrid, frozen);
        boolean blockedVertical   = isBlockedOnAxis(r, c, 1, boxGrid, frozen);
        return blockedHorizontal && blockedVertical;
    }

    /**
     * Returns true if the box at (r, c) cannot be pushed in either direction along the given axis.
     * axis 0 is horizontal (left/right), axis 1 is vertical (up/down).
     *
     * A push in one direction needs two things: the cell the box would land on must be a valid
     * destination, and the cell the player would stand on to push must be walkable.
     *
     * @param r       row of the box
     * @param c       column of the box
     * @param axis    0 for horizontal, 1 for vertical
     * @param boxGrid grid marking which cells have a box
     * @param frozen  grid marking which boxes are already confirmed stuck
     * @return true if the box cannot be pushed either way along this axis
     */
    private boolean isBlockedOnAxis(int r, int c, int axis, boolean[][] boxGrid, boolean[][] frozen) {
        int dRow1 = (axis == 1) ? -1 : 0;
        int dCol1 = (axis == 0) ? -1 : 0;
        int dRow2 = -dRow1;
        int dCol2 = -dCol1;

        //Push toward side 1: side 1 must be a valid landing spot, side 2 must be walkable
        boolean canPushToSide1 = !isBlockedSide(r, c, dRow1, dCol1, boxGrid, frozen, true)
                && !isBlockedSide(r, c, dRow2, dCol2, boxGrid, frozen, false);

        //Push toward side 2: side 2 must be a valid landing spot, side 1 must be walkable
        boolean canPushToSide2 = !isBlockedSide(r, c, dRow2, dCol2, boxGrid, frozen, true)
                && !isBlockedSide(r, c, dRow1, dCol1, boxGrid, frozen, false);

        return !canPushToSide1 && !canPushToSide2;
    }

    /**
     * Checks whether the neighboring cell at (r+dRow, c+dCol) blocks a push on this side.
     *
     * The cell plays one of two roles: if asDestination is true, it's where the box would land
     * (blocked by walls, dead squares, or stuck boxes); if false, it's where the player must
     * stand to push (blocked by walls or stuck boxes, but not dead squares since those only
     * restrict boxes, not the player).
     *
     * A neighboring box only blocks if it is itself confirmed stuck. A box that can still move
     * doesn't count as permanently blocking since it could be pushed out of the way first.
     *
     * @param r             row of the box being checked
     * @param c             column of the box being checked
     * @param dRow          row offset of the neighboring cell
     * @param dCol          column offset of the neighboring cell
     * @param boxGrid       grid marking which cells have a box
     * @param frozen        grid marking which boxes are already confirmed stuck
     * @param asDestination true if checking where the box would land, false if checking where the player stands
     * @return true if this side blocks the push
     */
    private boolean isBlockedSide(int r, int c, int dRow, int dCol, boolean[][] boxGrid, boolean[][] frozen, boolean asDestination) {
        int sideR = r + dRow;
        int sideC = c + dCol;

        if (sideR < 0 || sideR >= height || sideC < 0 || sideC >= width) {
            return true; //Off the grid
        }
        if (walls[sideR][sideC]) {
            return true;
        }
        if (asDestination && deadSquares[sideR][sideC]) {
            return true; //Box can't land on a dead square
        }
        if (boxGrid[sideR][sideC]) {
            return frozen[sideR][sideC]; //Only blocks if that box is also stuck
        }
        return false;
    }

    /**
     * Returns true if every box can still be matched to a distinct goal it can reach.
     * If no such matching exists, the puzzle is unsolvable from this state regardless
     * of how the boxes are moved around.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return true if a valid box-to-goal assignment still exists
     */
    private boolean hasGoalAssignment(List<int[]> boxes) {
        int n = boxes.size();
        if (n == 0)       return true;
        if (numGoals < n) return false;

        //Build the list of goals each box can reach
        List<List<Integer>> adjacency = new ArrayList<>();
        for (int[] box : boxes) {
            int br = box[0], bc = box[1];
            List<Integer> reachableGoals = new ArrayList<>();
            for (int g = 0; g < numGoals; g++)
                if (pushDist[g][br][bc] != Integer.MAX_VALUE)
                    reachableGoals.add(g);
            adjacency.add(reachableGoals);
        }

        //Try to match every box to a distinct goal using augmenting paths
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
     * Tries to find a goal for the given box as part of the matching in hasGoalAssignment.
     * If the best candidate goal is already taken by another box, it tries to move that box
     * to a different goal recursively.
     *
     * @param boxIndex       index of the box to match
     * @param adjacency      list of reachable goals for each box
     * @param visited        goals already tried in this round
     * @param matchGoalToBox current matching state
     * @return true if a valid match was found
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
     * Returns true if every box is currently sitting on a goal tile.
     *
     * @param boxes current box positions, each entry as {row, col}
     * @return true if the puzzle is solved
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
     *
     * state carries the box layout plus the player's canonical reachable-region cell, used
     * purely for hashing and deduplication. trueR and trueC carry the player's actual physical
     * position at this node, which is the cell the previously pushed box used to occupy, or the
     * puzzle's literal starting cell for the root node.
     *
     * Keeping these separate matters: two states with the same boxes and the same reachable
     * region are the same search state regardless of exactly where in that region the player
     * is standing. But the canonical cell is just the top-left-most free cell, not necessarily
     * where the player actually is. Reconstructing a walkable move string requires starting from
     * the true position, not the canonical one.
     *
     * g and totalMoves together form the lexicographic search cost: g (pushes) is the primary
     * criterion the heuristic bounds, while totalMoves (every keypress, walking included) is a
     * secondary tie-break so that among push-count-tied routes, the one needing less walking wins.
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
     * Unpacks a State's sorted box array back into a List of int arrays,
     * the shape every Part 1-3 helper expects.
     *
     * @param state the state to unpack
     * @return the same box positions as a list
     */
    private List<int[]> stateToBoxList(State state) {
        List<int[]> list = new ArrayList<>(state.boxes.length);
        for (int[] box : state.boxes) {
            list.add(new int[]{box[0], box[1]});
        }
        return list;
    }

    /**
     * Generates every legal successor of the current node by trying to push each box one step
     * in each of the four directions, and enqueues the survivors onto the open list.
     *
     * A push requires: the player can reach the cell behind the box without pushing anything
     * else first; the destination cell is in bounds, not a wall, not a dead square, and not
     * occupied by another box; and the resulting configuration is not a deadlock. Successors
     * that pass all three are only enqueued if they improve on the best known cost to that state.
     *
     * @param current  the node being expanded
     * @param boxes    the current box positions, already unpacked
     * @param open     the A* open list
     * @param bestCost best known cost seen so far for each visited state
     * @param closed   states that have already been fully expanded
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
                // to find the canonical cell. No pathTo() call needed, we already have the
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

                // Reconstruct walk path using the parent map from BFS 1, O(path length) only,
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
     * Walks the parent chain from the goal node back to the root, collecting each edge's move
     * string, then re-emits them in forward order.
     *
     * @param goalNode the node whose box configuration is solved
     * @return the full u/d/l/r move string from start to solution
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
     * Packs a (pushes, totalMoves) pair into a single long so two lexicographic costs
     * can be compared with one numeric comparison.
     *
     * @param pushes     number of pushes in this cost
     * @param totalMoves number of real keypresses (pushes + walking) in this cost
     * @return a single comparable long encoding both, pushes as the more significant component
     */
    private static long packCost(int pushes, int totalMoves) {
        return (long) pushes * 1_000_000L + totalMoves;
    }
}
