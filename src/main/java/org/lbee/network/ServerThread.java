package org.lbee.network;

import org.lbee.protocol.Message;

import java.io.*;
import java.net.Socket;

public class ServerThread extends Thread {

    private final Socket socket;
    private final MessageBucket networkMock;

    public ServerThread(Socket socket, MessageBucket networkMock) {
        this.socket = socket;
        this.networkMock = networkMock;
    }

    public void run() {
        try {
            InputStream input = socket.getInputStream();
            BufferedReader reader = new BufferedReader(new InputStreamReader(input));

            OutputStream output = socket.getOutputStream();
            PrintWriter writer = new PrintWriter(output, true);

            String text;

            do {
                text = reader.readLine();

                // Message send
                if (text.startsWith("s:")) {
                    // Get message data
                    String messageData = text.substring(2, text.length());
                    // Create message object from data
                    Message message = new Message(messageData.split(";"));
                    // Put message on queue
                    networkMock.put(message);
                    writer.println("ack");
                    System.out.println(message);
                }
                // Message collect (receive)
                else if (text.startsWith("r:")) {
                    String dest = text.substring(2, text.length());
                    // Search message
                    Message message = networkMock.take(dest);
                    // Send message to client that request it
                    if (message != null)
                        writer.println(message.toString());
                    else
                        writer.println("null");
                }

            } while (!text.equals("bye"));
            System.out.println("A client quit.");
            socket.close();
        } catch (IOException | InterruptedException ex) {
            System.out.println("Server exception: " + ex.getMessage());
            ex.printStackTrace();
        }
    }
}
