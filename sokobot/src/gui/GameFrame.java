package gui;

import javax.swing.JFrame;
import java.awt.GridLayout;
import java.io.FileWriter;
import reader.MapData;

public class GameFrame extends JFrame {
  private GamePanel mainPanel;
  private MapData mapData;

  public GameFrame(MapData mapData) {
    this.mapData = mapData;

    this.setSize(800, 600);
    this.setLayout(new GridLayout(0, 1));
    this.setLocationRelativeTo(null);
    this.setTitle("Sokoban");
    this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

    this.mainPanel = new GamePanel(this);
    this.add(mainPanel);

    this.mainPanel.loadMap(mapData);
    this.setVisible(true);
  }

  public void initiateFreePlay() {
    this.mainPanel.initiateFreePlay();
  }

  public void initiateSolution() {
    this.mainPanel.initiateSolution();
  }

  public void initiateCheck() {
    this.mainPanel.initiateSolution();
    this.mainPanel.startThinking(true);
  }

  public void resolveTest(double thinkingTime, int progress, int boxes, int moves) {
    try {
      FileWriter writer = new FileWriter("temp.txt");
      String status = progress == boxes ? "PASS" : "FAIL";
      writer.write(String.format("%.2f", thinkingTime) + " " + status + " " + moves);
      writer.close();
    } catch (Exception ex) {
      System.err.print("Error writing to temporary file.\n");
    } finally {

      System.exit(1);
    }
  }
}