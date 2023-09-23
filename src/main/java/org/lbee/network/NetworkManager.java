package org.lbee.network;

import org.lbee.helpers.Helper;
import org.lbee.protocol.Message;

import java.io.*;
import java.net.Socket;

public class NetworkManager {
    // interval between checking if a message has been received
    private final static int INTERVAL_BETWEEN_MESSAGE_POLL = 10;
    // used to simulate a timeout for message receive
    private final static int FACTOR = 2;
    
    private final InputStream inputStream;
    private final PrintWriter writer;

    public NetworkManager(Socket socket) throws IOException {
        this.inputStream = socket.getInputStream();
        OutputStream outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
    }

    public boolean send(Message message) throws IOException {
        // Send message to server
        writer.println("s:" + message.toString());
        // Read response
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    public Message receive(String processName) throws IOException {
        // Request for message destined to me
        writer.println("r:" + processName);
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        if (data.equals("null"))
            return null;
        else {
            String[] components = data.split(";");
            return new Message(components);
        }
    }

    public Message syncReceive(String processName, int timeout) throws IOException, TimeOutException {
        if (Helper.next(timeout*FACTOR) < timeout) {
            throw new TimeOutException();
        }
        while (true) {
            // Request for message destined to me
            writer.println("r:" + processName);
            BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
            String data = reader.readLine();

            // Data is not null, return
            if (!data.equals("null")) {
                String[] components = data.split(";");
                return new Message(components);
            }

            // Data is null, block INTERVAL_BETWEEN_MESSAGE_POLL ms
            try {
                Thread.sleep(INTERVAL_BETWEEN_MESSAGE_POLL);
            } catch (InterruptedException e) {
            }
        }
    }

    public void sendRaw(String s) {
        writer.println(s);
    }

}
