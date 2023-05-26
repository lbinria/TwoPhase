package org.lbee;

import org.lbee.models.Message;

import java.io.*;
import java.net.Socket;

public class NetworkManager {

    private final InputStream inputStream;
    private final PrintWriter writer;

    public NetworkManager(Socket socket) throws IOException {
        this.inputStream = socket.getInputStream();
        OutputStream outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
    }

    protected boolean send(Message message) throws IOException {
        // Send message to server
        writer.println("s:" + message.toString());
        // Read response
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    protected Message receive(String processName) throws IOException {
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

    protected void sendRaw(String s) {
        writer.println(s);
    }

}
