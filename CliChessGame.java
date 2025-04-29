import java.io.Console; // Import Console class
import java.io.IOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.util.ArrayList; // Needed for move generation
import java.util.List;    // Needed for move generation
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
// You need to add the org.json library to your project.
// If using Maven, add this to your pom.xml:
// <dependency>
//     <groupId>org.json</groupId>
//     <artifactId>json</artifactId>
//     <version>20231013</version> // Or a later version
// </dependency>
// Or download the JAR from https://mvnrepository.com/artifact/org.json/json
import org.json.JSONObject;
import org.json.JSONArray;

/**
 * A command-line interface (CLI) Chess game framework.
 * Allows a human player (White) to play against a Gemini AI (Black).
 * Includes a chat feature to talk to the AI during the player's turn.
 * Requires a Gemini API key (input is masked if run in a standard terminal).
 * Features improved AI prompting and internal move validation.
 * AI will retry making a move if its initial attempt is invalid, up to a limit.
 * **New:** Added structure for check and checkmate detection.
 */
public class CliChessGame {

    // --- Constants ---
    private static final int BOARD_SIZE = 8;
    private static final int MAX_AI_RETRIES = 3; // Max attempts for AI per turn
    // Internal representation uses 6 chars for alignment
    private static final String EMPTY_SQUARE = "[    ]";
    private static final String W_ROK = "[WROK]"; private static final String W_KNT = "[WKNT]";
    private static final String W_BSH = "[WBSH]"; private static final String W_QUN = "[WQUN]";
    private static final String W_KNG = "[WKNG]"; private static final String W_PWN = "[WPWN]";
    private static final String B_ROK = "[BROK]"; private static final String B_KNT = "[BKNT]";
    private static final String B_BSH = "[BBSH]"; private static final String B_QUN = "[BQUN]";
    private static final String B_KNG = "[BKNG]"; private static final String B_PWN = "[BPWN]";

    // Gemini API Configuration
    private static final String GEMINI_API_ENDPOINT = "https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-flash-preview-04-17:generateContent?key=";
    private String geminiApiKey;

    // --- Game State ---
    private String[][] board;
    private boolean isWhiteTurn = true;
    private Scanner scanner;
    private HttpClient httpClient;
    private String lastInvalidAiMoveAttempt = null; // Store the last failed move for the retry prompt
    // TODO: Add state for castling rights, en passant target square if implementing those rules

    /** Constructor */
    public CliChessGame() {
        board = new String[BOARD_SIZE][BOARD_SIZE];
        scanner = new Scanner(System.in);
        httpClient = HttpClient.newHttpClient();
        initializeBoard();
    }

    /** Sets up the initial board state */
    private void initializeBoard() {
        // Place black pieces
        board[0][0] = B_ROK; board[0][1] = B_KNT; board[0][2] = B_BSH; board[0][3] = B_QUN;
        board[0][4] = B_KNG; board[0][5] = B_BSH; board[0][6] = B_KNT; board[0][7] = B_ROK;
        for (int col = 0; col < BOARD_SIZE; col++) { board[1][col] = B_PWN; }
        // Place white pieces
        board[7][0] = W_ROK; board[7][1] = W_KNT; board[7][2] = W_BSH; board[7][3] = W_QUN;
        board[7][4] = W_KNG; board[7][5] = W_BSH; board[7][6] = W_KNT; board[7][7] = W_ROK;
        for (int col = 0; col < BOARD_SIZE; col++) { board[6][col] = W_PWN; }
        // Fill empty squares
        for (int row = 2; row < 6; row++) {
            for (int col = 0; col < BOARD_SIZE; col++) { board[row][col] = EMPTY_SQUARE; }
        }
    }

    /** Displays the board using the internal representation */
    public void displayBoard() {
        String separator = "   +------+------+------+------+------+------+------+------+";
        System.out.println("\n" + separator);
        for (int row = 0; row < BOARD_SIZE; row++) {
            System.out.print(" " + (8 - row) + " "); // Print rank number
            for (int col = 0; col < BOARD_SIZE; col++) { System.out.print("|" + board[row][col]); }
            System.out.println("|");
            System.out.println(separator);
        }
        // Print file letters
        System.out.print("      ");
        for (int col = 0; col < BOARD_SIZE; col++) { System.out.print((char)('a' + col) + "      "); }
        System.out.println("\n");
    }

    /** Converts algebraic notation (e.g., "e4") to [row, col] */
    private int[] algebraicToIndex(String algebraicNotation) {
        if (algebraicNotation == null || algebraicNotation.length() != 2) { return null; }
        char fileChar = algebraicNotation.toLowerCase().charAt(0);
        char rankChar = algebraicNotation.charAt(1);
        if (fileChar < 'a' || fileChar > 'h' || rankChar < '1' || rankChar > '8') { return null; }
        int col = fileChar - 'a';
        int row = '8' - rankChar; // Chess ranks are 1-8 bottom-up, array rows are 0-7 top-down
        return new int[]{row, col};
    }

    /** Converts [row, col] to algebraic notation */
    private String indexToAlgebraic(int row, int col) {
        if (row < 0 || row >= BOARD_SIZE || col < 0 || col >= BOARD_SIZE) { return null; }
        char file = (char) ('a' + col);
        char rank = (char) ('8' - row);
        return "" + file + rank;
    }

    /** Gets piece at [row, col] using internal representation */
    private String getPieceAt(int row, int col) {
        if (row < 0 || row >= BOARD_SIZE || col < 0 || col >= BOARD_SIZE) { return null; }
        return board[row][col];
    }

     /** Finds the coordinates of the specified king.
     * @param isWhiteKing true to find the white king, false for the black king.
     * @return int[] coordinates [row, col] of the king, or null if not found (should not happen in a valid game).
     */
    private int[] findKing(boolean isWhiteKing) {
        String kingToFind = isWhiteKing ? W_KNG : B_KNG;
        for (int r = 0; r < BOARD_SIZE; r++) {
            for (int c = 0; c < BOARD_SIZE; c++) {
                if (board[r][c].equals(kingToFind)) {
                    return new int[]{r, c};
                }
            }
        }
        return null; // Should not happen
    }

    /**
     * Checks if the specified king is currently under attack (in check).
     * @param isWhiteKingToCheck true to check the white king, false for the black king.
     * @return true if the specified king is in check, false otherwise.
     */
    private boolean isKingInCheck(boolean isWhiteKingToCheck) {
        int[] kingCoords = findKing(isWhiteKingToCheck);
        if (kingCoords == null) {
            // This means the king was captured - game should have already ended!
            // Or the board is in an invalid state.
            // System.err.println("Error: King not found on board during check detection!");
            return false; // Or handle as a game-ending error
        }
        int kingRow = kingCoords[0];
        int kingCol = kingCoords[1];
        char opponentColor = isWhiteKingToCheck ? 'B' : 'W';

        // Iterate through all opponent pieces and see if they can attack the king's square
        for (int r = 0; r < BOARD_SIZE; r++) {
            for (int c = 0; c < BOARD_SIZE; c++) {
                String piece = board[r][c];
                if (!piece.equals(EMPTY_SQUARE) && piece.charAt(1) == opponentColor) {
                    // Check if this opponent piece can legally move to the king's square
                    // We use isValidMove, but pass 'false' for checkTurn because we are checking
                    // the opponent's potential move, not their actual turn.
                    if (isValidMove(new int[]{r, c}, kingCoords, false)) {
                        // System.out.println("Check detected: " + piece + " at " + indexToAlgebraic(r,c) + " attacks King at " + indexToAlgebraic(kingRow, kingCol));
                        return true; // King is in check
                    }
                }
            }
        }
        return false; // King is not in check
    }


    /**
     * Generates all possible legal moves for the specified player.
     * NOTE: This is a complex function. This implementation is a STUB and
     * does NOT correctly filter moves that leave the king in check.
     * A full implementation requires generating all pseudo-legal moves and then
     * checking each one to see if it results in the king being safe.
     *
     * @param isWhitePlayer true for White's moves, false for Black's moves.
     * @return A List of valid move coordinates [[startRow, startCol], [endRow, endCol]].
     * Returns an empty list if no legal moves exist.
     */
    private List<int[][]> getAllLegalMoves(boolean isWhitePlayer) {
        List<int[][]> legalMoves = new ArrayList<>();
        char playerColor = isWhitePlayer ? 'W' : 'B';

        for (int startRow = 0; startRow < BOARD_SIZE; startRow++) {
            for (int startCol = 0; startCol < BOARD_SIZE; startCol++) {
                String piece = board[startRow][startCol];
                if (!piece.equals(EMPTY_SQUARE) && piece.charAt(1) == playerColor) {
                    // Found a piece belonging to the player
                    for (int endRow = 0; endRow < BOARD_SIZE; endRow++) {
                        for (int endCol = 0; endCol < BOARD_SIZE; endCol++) {
                            int[] startCoords = {startRow, startCol};
                            int[] endCoords = {endRow, endCol};
                            // Check if the move is valid according to piece rules (ignoring check for now)
                            if (isValidMove(startCoords, endCoords, false)) { // Use false for checkTurn here
                                // --- !!! CRITICAL MISSING STEP !!! ---
                                // A *real* implementation MUST simulate the move here:
                                // 1. Temporarily make the move on a copy of the board.
                                // 2. Call isKingInCheck() for the current player on the temporary board.
                                // 3. If the king is NOT in check after the move, THEN add it to legalMoves.
                                // 4. Undo the temporary move.
                                // --- End Missing Step ---

                                // For this stub, we just add any move valid by piece rules.
                                // This means it won't correctly identify checkmate/stalemate yet.
                                legalMoves.add(new int[][]{startCoords, endCoords});
                            }
                        }
                    }
                }
            }
        }
        // System.out.println("Generated " + legalMoves.size() + " pseudo-legal moves for " + (isWhitePlayer ? "White" : "Black"));
        return legalMoves;
    }

     /**
     * Checks if the current player is checkmated or stalemated.
     * @param isWhitePlayer The player whose turn it currently is.
     * @return "CHECKMATE", "STALEMATE", or "NONE".
     */
    private String getGameEndState(boolean isWhitePlayer) {
        boolean inCheck = isKingInCheck(isWhitePlayer);
        // *** IMPORTANT: Using the stubbed getAllLegalMoves ***
        // This will likely NOT return the correct checkmate/stalemate status yet
        // until getAllLegalMoves is fully implemented to filter moves leaving king in check.
        List<int[][]> legalMoves = getAllLegalMoves(isWhitePlayer);

        if (legalMoves.isEmpty()) {
            if (inCheck) {
                return "CHECKMATE";
            } else {
                return "STALEMATE";
            }
        }
        return "NONE"; // Game continues
    }


    /**
     * Performs basic move validation (bounds, start empty, capturing own piece).
     * This is called by the more comprehensive `isValidMove`.
     * @param startCoords [row, col] of starting square
     * @param endCoords [row, col] of ending square
     * @param checkTurn If true, enforces that the piece moved matches the current player's turn.
     * @return true if basic checks pass, false otherwise.
     */
    private boolean isValidMoveBasic(int[] startCoords, int[] endCoords, boolean checkTurn) {
        if (startCoords == null || endCoords == null) {
            // This check is redundant if parseMoveInput is used, but good practice
            // System.out.println("Invalid coordinate format.");
            return false;
        }
        int startRow = startCoords[0], startCol = startCoords[1], endRow = endCoords[0], endCol = endCoords[1];

        // Check bounds
        if (startRow < 0 || startRow >= BOARD_SIZE || startCol < 0 || startCol >= BOARD_SIZE ||
            endRow < 0 || endRow >= BOARD_SIZE || endCol < 0 || endCol >= BOARD_SIZE) {
            // Avoid printing during internal checks like isKingInCheck
            // System.out.println("Move " + indexToAlgebraic(startRow, startCol) + indexToAlgebraic(endRow, endCol) + " is out of board bounds.");
            return false;
        }

        // Check if start square is empty
        String piece = getPieceAt(startRow, startCol);
        if (piece.equals(EMPTY_SQUARE)) {
             // Avoid printing during internal checks
             // System.out.println("Starting square " + indexToAlgebraic(startRow, startCol) + " is empty.");
             return false;
        }

        // Check turn if required (only for actual player moves, not internal checks)
        if (checkTurn) {
            char pieceColor = piece.charAt(1); // W or B
            if ((isWhiteTurn && pieceColor != 'W') || (!isWhiteTurn && pieceColor != 'B')) {
                System.out.println("It's not " + (isWhiteTurn ? "White's" : "Black's") + " turn or that's not your piece at " + indexToAlgebraic(startRow, startCol) + "."); return false;
            }
        }

        // Check if capturing own piece
        String destinationPiece = getPieceAt(endRow, endCol);
        if (!destinationPiece.equals(EMPTY_SQUARE)) {
            char startColor = piece.charAt(1);
            char destinationColor = destinationPiece.charAt(1);
            if (startColor == destinationColor) {
                 // Avoid printing during internal checks
                 // System.out.println("Cannot capture your own piece (" + destinationPiece + ") at " + indexToAlgebraic(endRow, endCol) + ".");
                 return false;
            }
        }

        // Check if start and end are the same
        if (startRow == endRow && startCol == endCol) {
             // Avoid printing during internal checks
             // System.out.println("Start and end squares cannot be the same.");
             return false;
        }

        return true; // Basic checks passed
    }

    /**
     * Performs comprehensive move validation, including piece-specific rules.
     * Calls isValidMoveBasic first.
     * **NOTE:** This does NOT currently validate against moving into check.
     * @param startCoords [row, col] of starting square
     * @param endCoords [row, col] of ending square
     * @param checkTurn If true, enforces that the piece moved matches the current player's turn.
     * @return true if the move is valid according to chess rules (excluding check), false otherwise.
     */
    private boolean isValidMove(int[] startCoords, int[] endCoords, boolean checkTurn) {
        // 1. Basic Checks (Bounds, Start Empty, Own Piece Capture, Turn Enforcement if checkTurn=true)
        if (!isValidMoveBasic(startCoords, endCoords, checkTurn)) {
            return false;
        }

        int startRow = startCoords[0], startCol = startCoords[1];
        int endRow = endCoords[0], endCol = endCoords[1];
        String piece = getPieceAt(startRow, startCol);
        char pieceColor = piece.charAt(1); // W or B
        String pieceType = piece.substring(2, 4); // RO, KN, BS, QU, KG, PW

        String targetPiece = getPieceAt(endRow, endCol);
        boolean isCapture = !targetPiece.equals(EMPTY_SQUARE);

        // --- Piece Specific Logic ---
        switch (pieceType) {
            case "PW": // Pawn
                int direction = (pieceColor == 'W') ? -1 : 1; // White moves up (-1), Black moves down (+1)
                int rowDiff = endRow - startRow;
                int colDiffAbs = Math.abs(endCol - startCol);

                // --- Standard 1-square move ---
                if (colDiffAbs == 0 && !isCapture && rowDiff == direction) {
                    return true; // Valid 1-square forward move
                }
                // --- Initial 2-square move ---
                int initialRow = (pieceColor == 'W') ? 6 : 1;
                if (colDiffAbs == 0 && !isCapture && startRow == initialRow && rowDiff == 2 * direction) {
                    // Check if path is clear for 2-square move
                    if (getPieceAt(startRow + direction, startCol).equals(EMPTY_SQUARE)) {
                        return true; // Valid 2-square initial move
                    } else {
                         // Avoid printing during internal checks
                         // System.out.println("Invalid Pawn move: Path blocked for 2-square advance.");
                         return false;
                    }
                }
                // --- Standard Capture ---
                if (colDiffAbs == 1 && isCapture && rowDiff == direction) {
                    return true; // Valid diagonal capture
                }
                // --- TODO: En Passant ---
                // --- TODO: Promotion ---

                // Avoid printing during internal checks
                // System.out.println("Invalid Pawn move: " + indexToAlgebraic(startRow, startCol) + " to " + indexToAlgebraic(endRow, endCol));
                return false; // Failed pawn logic

            case "RO": // Rook
                 if ((startRow == endRow || startCol == endCol) && isPathClear(startCoords, endCoords)) {
                     return true;
                 }
                 // Avoid printing during internal checks
                 // System.out.println("Invalid Rook move: Must be horizontal/vertical and path must be clear.");
                 return false;

            case "KN": // Knight
                int rDelta = Math.abs(startRow - endRow);
                int cDelta = Math.abs(startCol - endCol);
                if ((rDelta == 2 && cDelta == 1) || (rDelta == 1 && cDelta == 2)) {
                    return true; // Knight jumps, doesn't need clear path
                }
                 // Avoid printing during internal checks
                 // System.out.println("Invalid Knight move: Must be L-shape (2x1 or 1x2).");
                return false;

            case "BS": // Bishop
                 if (Math.abs(startRow - endRow) == Math.abs(startCol - endCol) && isPathClear(startCoords, endCoords)) {
                    return true;
                 }
                 // Avoid printing during internal checks
                 // System.out.println("Invalid Bishop move: Must be diagonal and path must be clear.");
                 return false;

            case "QU": // Queen
                 if (((startRow == endRow || startCol == endCol) || // Rook-like move
                     (Math.abs(startRow - endRow) == Math.abs(startCol - endCol))) // Bishop-like move
                     && isPathClear(startCoords, endCoords)) { // Path must be clear for both
                     return true;
                 }
                  // Avoid printing during internal checks
                  // System.out.println("Invalid Queen move: Must be horizontal, vertical, or diagonal and path must be clear.");
                 return false;

            case "KG": // King
                int rKingDelta = Math.abs(startRow - endRow);
                int cKingDelta = Math.abs(startCol - endCol);
                if (rKingDelta <= 1 && cKingDelta <= 1) {
                    // --- !!! CRITICAL MISSING STEP for full validation !!! ---
                    // A real implementation needs to check if moving the king here
                    // would place it in check from an opponent piece.
                    // --- End Missing Step ---
                    // TODO: Add castling logic
                    return true; // Valid 1-square move (basic)
                }
                 // Avoid printing during internal checks
                 // System.out.println("Invalid King move: Can only move 1 square in any direction (excluding castling).");
                return false;

            default:
                // System.out.println("Unknown piece type encountered in validation: " + pieceType);
                return false; // Should not happen
        }
    }

    /**
     * Helper method to check if the path between two squares is clear (for Rook, Bishop, Queen).
     * Does not check the start/end squares themselves.
     * Assumes the move is either purely horizontal, vertical, or purely diagonal.
     * @param startCoords [row, col]
     * @param endCoords [row, col]
     * @return true if the path is clear, false otherwise. Returns true for Knight moves as path doesn't matter.
     */
    private boolean isPathClear(int[] startCoords, int[] endCoords) {
        int r1 = startCoords[0], c1 = startCoords[1];
        int r2 = endCoords[0], c2 = endCoords[1];

        // Knight moves don't require a clear path
        String piece = getPieceAt(r1, c1);
        // Added null check for safety, though getPieceAt should handle bounds
        if (piece == null || piece.equals(EMPTY_SQUARE)) return false; // Cannot check path for empty square
        if (piece.substring(2, 4).equals("KN")) {
            return true;
        }

        int rStep = Integer.compare(r2, r1); // 0, 1, or -1
        int cStep = Integer.compare(c2, c1); // 0, 1, or -1

        // Check if move is purely horizontal, vertical, or diagonal
        boolean isStraight = (r1 == r2 || c1 == c2);
        boolean isDiagonal = (Math.abs(r1 - r2) == Math.abs(c1 - c2));
        if (!isStraight && !isDiagonal) {
             return false;
        }

        int currentRow = r1 + rStep;
        int currentCol = c1 + cStep;

        // Iterate along the path, excluding the start and end squares
        while (currentRow != r2 || currentCol != c2) {
            if (currentRow < 0 || currentRow >= BOARD_SIZE || currentCol < 0 || currentCol >= BOARD_SIZE) {
                 return false; // Should be prevented by initial bounds check
            }
            if (!board[currentRow][currentCol].equals(EMPTY_SQUARE)) {
                return false; // Path is blocked
            }
            currentRow += rStep;
            currentCol += cStep;
        }
        return true; // Path is clear
    }

    /** Executes a move on the internal board */
    private void makeMove(int[] startCoords, int[] endCoords) {
        String pieceToMove = board[startCoords[0]][startCoords[1]];
        String capturedPiece = board[endCoords[0]][endCoords[1]];

        // Check if the captured piece is a King - this indicates game over
        // (This is a simplified check; proper checkmate logic is more robust)
        if (!capturedPiece.equals(EMPTY_SQUARE) && capturedPiece.substring(2, 4).equals("KG")) {
             System.out.println("Captured King: " + capturedPiece + " at " + indexToAlgebraic(endCoords[0], endCoords[1]));
             // We'll handle the game end message in the main loop after the move
        } else if (!capturedPiece.equals(EMPTY_SQUARE)) {
            System.out.println("Captured: " + capturedPiece + " at " + indexToAlgebraic(endCoords[0], endCoords[1]));
        }

        board[endCoords[0]][endCoords[1]] = pieceToMove;
        board[startCoords[0]][startCoords[1]] = EMPTY_SQUARE;

        // TODO: Handle promotion, update castling rights, set en passant target square if applicable
    }

    /** Parses move input (e.g., "e2e4" or "e2 e4") */
    private int[][] parseMoveInput(String input) {
        // Regex allows optional space between squares, case-insensitive
        Pattern pattern = Pattern.compile("^([a-h][1-8])\\s?([a-h][1-8])$", Pattern.CASE_INSENSITIVE);
        Matcher matcher = pattern.matcher(input.trim());
        if (matcher.matches()) {
            String startAlg = matcher.group(1);
            String endAlg = matcher.group(2);
            int[] startCoords = algebraicToIndex(startAlg);
            int[] endCoords = algebraicToIndex(endAlg);
            if (startCoords != null && endCoords != null) {
                return new int[][]{startCoords, endCoords};
            }
        }
        // Return null if not in move format, indicating it might be chat or invalid
        return null;
    }

    /**
     * Creates board state string for API using a more standard notation.
     * Example: White Rook -> R, Black Pawn -> p, Empty -> .
     * Uppercase for White, lowercase for Black.
     * @return Formatted string representation of the board for the API prompt.
     */
    private String getBoardStateForApi() {
        StringBuilder sb = new StringBuilder();
        for (int row = 0; row < BOARD_SIZE; row++) {
            sb.append(8 - row).append(" "); // Rank number
            for (int col = 0; col < BOARD_SIZE; col++) {
                String piece = board[row][col];
                String apiPiece;
                if (piece.equals(EMPTY_SQUARE)) {
                    apiPiece = "."; // Simple dot for empty
                } else {
                    char color = piece.charAt(1); // W or B
                    char typeInitial = ' ';
                    String type = piece.substring(2, 4); // RO, KN, BS, QU, KG, PW
                    switch (type) {
                        case "RO": typeInitial = 'R'; break;
                        case "KN": typeInitial = 'N'; break; // N for Knight in standard notation
                        case "BS": typeInitial = 'B'; break;
                        case "QU": typeInitial = 'Q'; break;
                        case "KG": typeInitial = 'K'; break;
                        case "PW": typeInitial = 'P'; break;
                        default: typeInitial = '?'; break; // Should not happen
                    }
                    // Use uppercase for White, lowercase for Black
                    apiPiece = (color == 'W') ? "" + Character.toUpperCase(typeInitial) : "" + Character.toLowerCase(typeInitial);
                }
                // Ensure consistent spacing for alignment in the prompt
                sb.append(String.format("%-3s", apiPiece)); // Pad with spaces to width 3
            }
            sb.append("\n");
        }
        // Add file letters at the bottom
        sb.append("   "); // Align with board start
        for (int col = 0; col < BOARD_SIZE; col++) {
            sb.append(String.format("%-3s", (char)('a' + col)));
        }
        sb.append("\n");
        return sb.toString();
    }

    /** Main game loop - Uses Console for masked API key input */
    public void startGame() {
        System.out.println("Welcome to CLI Chess!");

        // --- Get API Key ---
        Console console = System.console();
        if (console != null) {
            char[] apiKeyChars = console.readPassword("Please enter your Gemini API Key: ");
            geminiApiKey = new String(apiKeyChars);
            java.util.Arrays.fill(apiKeyChars, ' ');
        } else {
            System.out.print("WARNING: Console not available. API Key will be visible.\nPlease enter your Gemini API Key: ");
            geminiApiKey = scanner.nextLine().trim();
        }
        if (geminiApiKey == null || geminiApiKey.isEmpty()) {
             System.out.println("API Key cannot be empty. Exiting."); return;
        }
        // --- End Get API Key ---

        System.out.println("\nEnter moves in algebraic notation (e.g., 'e2 e4' or 'e2e4').");
        System.out.println("Type anything else to chat with the AI (during your turn).");
        System.out.println("Type 'quit' to exit.");

        boolean gameOver = false;
        String endMessage = "";

        // Main game loop driven by turn handlers
        while (!gameOver) {
            displayBoard();

            // Check for game end condition *before* the current player moves
            // (Based on the state left by the *previous* player's move)
            String endState = getGameEndState(isWhiteTurn);
            if (!endState.equals("NONE")) {
                gameOver = true;
                if (endState.equals("CHECKMATE")) {
                    endMessage = "CHECKMATE! " + (isWhiteTurn ? "Black" : "White") + " wins!";
                } else { // Stalemate
                    endMessage = "STALEMATE! It's a draw!";
                }
                break; // Exit the loop immediately
            }

            // If game not over, proceed with the turn
            if (isWhiteTurn) {
                System.out.println("--- Your Turn (White) ---");
                 if (isKingInCheck(true)) { System.out.println("!!! White King is in Check !!!"); }
                handlePlayerTurn(); // This will set isWhiteTurn = false after a successful move
            } else {
                System.out.println("--- AI's Turn (Black) ---");
                 if (isKingInCheck(false)) { System.out.println("!!! Black King is in Check !!!"); }
                handleAiTurn();     // This will set isWhiteTurn = true after attempting a move
            }
        } // End while loop

        // Game Over message
        displayBoard(); // Show final board state
        System.out.println("\n================ GAME OVER ================");
        System.out.println(endMessage);
        System.out.println("=========================================");
    }

     /**
     * Handles the logic for the human player's turn.
     * Allows for making moves or sending chat messages to the AI.
     * Sets isWhiteTurn to false only after a successful move.
     */
    private void handlePlayerTurn() {
         boolean turnEnded = false; // Flag to indicate if the player's turn should end (move made)
         while (!turnEnded) {
             System.out.print("Enter move or chat message: ");
             String input = scanner.nextLine().trim();

             if ("quit".equalsIgnoreCase(input)) {
                 System.out.println("Exiting game. Goodbye!");
                 System.exit(0);
             }

             // Try parsing as a move first
             int[][] moveCoords = parseMoveInput(input);

             if (moveCoords != null) {
                 // It looks like a move command
                 int[] startCoords = moveCoords[0];
                 int[] endCoords = moveCoords[1];

                 // Use the comprehensive validation, enforcing turn check
                 if (isValidMove(startCoords, endCoords, true)) {
                     // --- Check if move leaves king in check (Simplified - needs full move generation) ---
                     // Temporarily make move
                     String pieceAtStart = board[startCoords[0]][startCoords[1]];
                     String pieceAtEnd = board[endCoords[0]][endCoords[1]];
                     board[endCoords[0]][endCoords[1]] = pieceAtStart;
                     board[startCoords[0]][startCoords[1]] = EMPTY_SQUARE;

                     boolean leavesKingInCheck = isKingInCheck(true); // Check white king

                     // Undo temporary move
                     board[startCoords[0]][startCoords[1]] = pieceAtStart;
                     board[endCoords[0]][endCoords[1]] = pieceAtEnd;
                     // --- End Check ---

                     if (leavesKingInCheck) {
                          System.out.println("Invalid move: Cannot leave your King in check.");
                     } else {
                         makeMove(startCoords, endCoords); // Make the move permanently
                         turnEnded = true; // Valid move made, exit this loop
                         isWhiteTurn = false; // Set up for AI's turn next iteration of main loop
                     }
                 } else {
                     // Error message printed by isValidMove or its sub-methods
                     // System.out.println("Invalid move. Try again or type a chat message."); // Already printed
                 }
             } else {
                 // Input is not a valid move format, treat as chat
                 System.out.println("Sending chat message to AI...");
                 handlePlayerChat(input);
                 // After chat, loop continues, player prompted again for move/chat
             }
         }
    }

    /**
     * Handles sending a chat message from the player to the AI and printing the response.
     * @param message The chat message from the player.
     */
    private void handlePlayerChat(String message) {
         String boardContext = getBoardStateForApi(); // Provide board context for chat too
         String prompt = "You are a chill chess AI playing Black against a human (White). " +
                         "The human just sent you a chat message instead of making a move. " +
                         "Respond conversationally to the message, keeping your chill persona. " +
                         "It is currently White's turn (human's turn to think). " +
                         "Here's the message: \"" + message + "\"\n\n" +
                         "For context, here is the current board state (Uppercase=White, Lowercase=Black, .=Empty):\n" +
                         "--------------------------------\n" +
                         boardContext +
                         "--------------------------------\n";

        // Reuse the API call logic, but just print the response
        callGeminiApi(prompt, false);
    }


     /**
     * Handles the AI's turn by generating a prompt, calling the API,
     * parsing the response, validating the move internally, and making the move if valid.
     * Retries prompting the AI if the move is invalid, up to MAX_AI_RETRIES.
     * Sets isWhiteTurn to true after attempting the move (success or failure).
     */
    private void handleAiTurn() {
        boolean aiMoveSuccessful = false;
        int retries = 0;
        lastInvalidAiMoveAttempt = null; // Reset last invalid attempt for the new turn

        while (!aiMoveSuccessful && retries < MAX_AI_RETRIES) {
            retries++;
            System.out.println("AI is thinking... (Attempt " + retries + "/" + MAX_AI_RETRIES + ")");
            String currentBoardState = getBoardStateForApi(); // Get the *exact* current state for this attempt

            String retryInstruction = "";
            if (retries > 1 && lastInvalidAiMoveAttempt != null) {
                // Make the retry prompt much stronger and more specific
                retryInstruction = String.format(
                    "ATTENTION: Your previous move attempt (%s) was INVALID according to chess rules. " +
                    "DO NOT suggest %s again. " +
                    "Analyze the board state below *very carefully* and choose a DIFFERENT and VALID move for Black (lowercase pieces). " +
                    "Ensure the move follows standard chess rules (piece movement, not capturing own pieces, clear paths for sliding pieces, etc.). " +
                    "Crucially, the move MUST NOT leave the Black King (k) in check.\n\n",
                    lastInvalidAiMoveAttempt, lastInvalidAiMoveAttempt
                );
            } else if (retries > 1) {
                 retryInstruction = "ATTENTION: Your previous move attempt was INVALID according to chess rules. " +
                    "Analyze the board state below *very carefully* and choose a DIFFERENT and VALID move for Black (lowercase pieces). " +
                    "Ensure the move follows standard chess rules and does not leave the Black King (k) in check.\n\n";
            }

            // --- Enhanced Prompt ---
            String prompt = "You are a helpful chess AI playing Black (lowercase letters: p, r, n, b, q, k). Your opponent plays White (uppercase letters: P, R, N, B, Q, K).\n" +
                            retryInstruction + // Add the strong retry instruction if applicable
                            "CRITICAL INSTRUCTION: Your task is to determine the *single best valid move* for Black for the *current turn only*, based *exclusively* on the board state provided below. Do NOT use any memory of previous turns or moves.\n" +
                            "It is currently Black's turn.\n\n" +
                            "BOARD STATE:\n" +
                            "--------------------------------\n" +
                             currentBoardState + // Pass the current, clearly formatted state
                            "--------------------------------\n\n" +
                            "Instructions:\n" +
                            "1. Analyze THIS board state ONLY.\n" +
                            "2. Identify all pieces belonging to Black (p, r, n, b, q, k).\n" +
                            "3. Determine all *valid* chess moves for Black's pieces according to the rules of chess. A move is ONLY valid if it does NOT leave the Black King (k) in check.\n" +
                            "4. Select the best valid move for Black.\n" +
                            "5. Briefly explain your reasoning (1-2 sentences).\n" +
                            "6. Output your chosen move on a single line prefixed EXACTLY with 'Move:'. Use standard algebraic notation (e.g., 'e7 e5', 'g8 f6', 'a7 a5'). Do not add extra characters or formatting around the move.\n\n" +
                            "Example response format:\n" +
                            "Developing the knight seems like a good idea.\n" +
                            "Move: g8f6\n\n" +
                            "Provide your actual move now:";
            // --- End Enhanced Prompt ---

            // Call the API expecting a move response. It now returns true if a valid move was made.
            aiMoveSuccessful = callGeminiApi(prompt, true); // Pass the prompt, expecting a move

            if (!aiMoveSuccessful && retries < MAX_AI_RETRIES) {
                 System.out.println("AI move attempt failed. Retrying...");
            }
        } // End while loop

        if (!aiMoveSuccessful) {
            System.out.println("!!! AI failed to provide a valid move after " + MAX_AI_RETRIES + " attempts. Skipping turn. !!!");
        }

        // Ensure turn switches back to player regardless of AI success/failure after retries
        isWhiteTurn = true;
    }

    /**
     * Generic method to call the Gemini API.
     * Can handle both move requests and chat responses.
     * If requesting a move, it attempts to parse, validate (internally), and execute it.
     * **Updates `lastInvalidAiMoveAttempt` if a move is suggested but invalid.**
     *
     * @param prompt The full prompt to send to the API.
     * @param isRequestingMove True if expecting a move in the response, false if expecting a chat response.
     * @return boolean True if a valid move was successfully processed and made, false otherwise. (Always false if isRequestingMove is false).
     */
    private boolean callGeminiApi(String prompt, boolean isRequestingMove) {
        boolean moveMadeSuccessfully = false; // Initialize success flag
        lastInvalidAiMoveAttempt = null; // Reset for this specific API call

        // Prepare the JSON request body
        JSONObject textPart = new JSONObject().put("text", prompt);
        JSONArray partsArray = new JSONArray().put(textPart);
        JSONObject contents = new JSONObject().put("parts", partsArray);
        JSONArray contentsArray = new JSONArray().put(contents);
        JSONObject requestBodyJson = new JSONObject().put("contents", contentsArray);
        String requestBody = requestBodyJson.toString();

        HttpRequest request = HttpRequest.newBuilder()
                .uri(URI.create(GEMINI_API_ENDPOINT + geminiApiKey))
                .header("Content-Type", "application/json")
                .POST(HttpRequest.BodyPublishers.ofString(requestBody))
                .build();

        try {
            HttpResponse<String> response = httpClient.send(request, HttpResponse.BodyHandlers.ofString());

            if (response.statusCode() == 200) {
                JSONObject responseJson = new JSONObject(response.body());
                String aiTextResponse = extractTextFromApiResponse(responseJson);

                if (aiTextResponse == null) {
                     System.out.println("!!! AI Error: Could not find text in the API response structure. !!!");
                     System.out.println("DEBUG: Raw AI Response Body: " + response.body());
                     return false; // Indicate failure
                }

                System.out.println("\nAI says: " + aiTextResponse.trim());

                if (isRequestingMove) {
                    // If we asked for a move, try to extract and validate it
                    String aiMoveAlgebraic = extractMoveFromResponse(aiTextResponse);
                    if (aiMoveAlgebraic != null) {
                        System.out.println("AI intends to move: " + aiMoveAlgebraic);
                        lastInvalidAiMoveAttempt = aiMoveAlgebraic; // Store the attempt *before* validation
                        int[][] aiMoveCoords = parseMoveInput(aiMoveAlgebraic); // Parse the extracted move

                        if (aiMoveCoords != null) {
                            int[] startCoords = aiMoveCoords[0];
                            int[] endCoords = aiMoveCoords[1];

                            // --- Internal Validation before making the move ---
                            String pieceToMove = getPieceAt(startCoords[0], startCoords[1]);

                            if (pieceToMove == null || pieceToMove.equals(EMPTY_SQUARE) || pieceToMove.charAt(1) != 'B') {
                                 System.out.println("!!! AI Error: Tried to move an invalid piece ("+ pieceToMove + " - is it empty or White's?) from " + indexToAlgebraic(startCoords[0], startCoords[1]) + ". !!!");
                            } else {
                                if (isValidMove(startCoords, endCoords, false)) {
                                     // --- Check if move leaves king in check (Simplified) ---
                                     String pieceAtStart = board[startCoords[0]][startCoords[1]];
                                     String pieceAtEnd = board[endCoords[0]][endCoords[1]];
                                     board[endCoords[0]][endCoords[1]] = pieceAtStart;
                                     board[startCoords[0]][startCoords[1]] = EMPTY_SQUARE;
                                     boolean leavesKingInCheck = isKingInCheck(false); // Check black king
                                     // Undo temporary move
                                     board[startCoords[0]][startCoords[1]] = pieceAtStart;
                                     board[endCoords[0]][endCoords[1]] = pieceAtEnd;
                                     // --- End Check ---

                                     if(leavesKingInCheck) {
                                         System.out.println("!!! AI Error: Suggested move " + aiMoveAlgebraic + " leaves the Black King in check. !!!");
                                     } else {
                                        makeMove(startCoords, endCoords); // Actually make the move
                                        System.out.println("AI successfully moved " + aiMoveAlgebraic);
                                        moveMadeSuccessfully = true; // Set flag on success
                                        lastInvalidAiMoveAttempt = null; // Clear invalid attempt on success
                                     }
                                } else {
                                    // Error message printed by isValidMove
                                    System.out.println("!!! AI Error: Provided invalid move " + aiMoveAlgebraic + " according to basic piece rules (validated internally). !!!");
                                }
                            }
                            // --- End Internal Validation ---

                        } else {
                             System.out.println("!!! AI Error: Could not parse AI move notation internally: '" + aiMoveAlgebraic + "'. !!!");
                        }
                    } else {
                        System.out.println("!!! AI Error: Could not extract 'Move:' notation (e.g., 'Move: e7e5') from response. !!!");
                        System.out.println("DEBUG: Full AI text response was: " + aiTextResponse);
                    }
                }
                // If !isRequestingMove, we just print the AI's chat response. moveMadeSuccessfully remains false.

            } else {
                System.err.println("API Error: HTTP status code " + response.statusCode());
                System.err.println("Response Body: " + response.body());
                System.out.println("AI turn/chat failed due to API error.");
            }

        } catch (IOException | InterruptedException e) {
            System.err.println("Error calling Gemini API: " + e.getMessage());
            e.printStackTrace();
            System.out.println("AI turn/chat failed due to network/request error.");
            Thread.currentThread().interrupt(); // Re-interrupt the thread
        } catch (org.json.JSONException e) {
             System.err.println("Error processing JSON response from API: " + e.getMessage());
             System.err.println("DEBUG: Raw response body: " + (e.getMessage().contains("HttpResponse") ? "Not available" : "See above HTTP error"));
             System.out.println("AI turn/chat failed due to JSON processing error.");
        } catch (Exception e) { // Catch unexpected errors
             System.err.println("An unexpected error occurred during API interaction: " + e.getMessage());
             e.printStackTrace();
             System.out.println("AI turn/chat failed due to unexpected error.");
        }

        return moveMadeSuccessfully; // Return the success status
    }

    /**
     * Safely extracts the text content from the Gemini API JSON response.
     * Navigates the expected JSON structure robustly.
     * @param responseJson The parsed JSON response object.
     * @return The extracted text string, or null if not found or if an error occurs.
     */
    private String extractTextFromApiResponse(JSONObject responseJson) {
         try {
             if (responseJson == null || !responseJson.has("candidates") || responseJson.isNull("candidates")) return null;
             JSONArray candidates = responseJson.getJSONArray("candidates");
             if (candidates.isEmpty() || candidates.isNull(0)) return null;
             JSONObject firstCandidate = candidates.getJSONObject(0);
             if (!firstCandidate.has("content") || firstCandidate.isNull("content")) return null;
             JSONObject content = firstCandidate.getJSONObject("content");
             if (!content.has("parts") || content.isNull("parts")) return null;
             JSONArray parts = content.getJSONArray("parts");
             if (parts.isEmpty() || parts.isNull(0)) return null;
             JSONObject firstPart = parts.getJSONObject(0);
             if (!firstPart.has("text") || firstPart.isNull("text")) return null;
             return firstPart.getString("text");
         } catch (org.json.JSONException e) {
             System.err.println("Error parsing JSON structure for text: " + e.getMessage());
             return null;
         }
    }


    /**
     * Extracts algebraic move notation (e.g., "e2e4") from the AI's text response.
     * Looks specifically for lines starting with "Move:" (case-insensitive).
     * @param aiResponse The full text response from the AI.
     * @return The extracted move string (e.g., "e2e4"), or null if not found.
     */
    private String extractMoveFromResponse(String aiResponse) {
        if (aiResponse == null || aiResponse.isEmpty()) {
            return null;
        }
        Pattern pattern = Pattern.compile("^\\s*Move:\\s*([a-h][1-8]\\s?[a-h][1-8])\\s*$", Pattern.CASE_INSENSITIVE | Pattern.MULTILINE);
        Matcher matcher = pattern.matcher(aiResponse.trim());
        if (matcher.find()) {
            return matcher.group(1).replaceAll("\\s+", "");
        }
        return null; // Move notation not found
    }

    /** Main method - Entry point */
    public static void main(String[] args) {
        // Check if the required JSON library is available at runtime
        try {
            Class.forName("org.json.JSONObject");
        } catch (ClassNotFoundException e) {
             System.err.println("\n--- ERROR ---");
             System.err.println("The required 'org.json' library was not found in the classpath.");
             System.err.println("Please ensure the org.json JAR file is included when compiling and running.");
             System.err.println("If using Maven/Gradle, add the dependency.");
             System.err.println("Download: https://mvnrepository.com/artifact/org.json/json");
             System.err.println("Example Run Command: java -cp \".:org.json-YYYYMMDD.jar\" CliChessGame");
             System.err.println("-------------\n");
             System.exit(1); // Exit if library is missing
        }

        // Create and start the game
        CliChessGame game = new CliChessGame();
        game.startGame();
    }
}
