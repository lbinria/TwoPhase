package org.lbee.twophase;

import java.io.*;
import java.net.Socket;
import java.util.HashSet;

public abstract class NetworkProcess2 {

    private final Socket socket;
    private final InputStream inputStream;
    private final OutputStream outputStream;
    private final PrintWriter writer;

    protected final LogicalClock logicalClock;

    private boolean shutdown;

    public boolean isShutdown() { return shutdown; }
    protected void shutdown() { shutdown = true; }

    public NetworkProcess2(Socket socket) throws IOException {
        this.socket = socket;
        this.inputStream = socket.getInputStream();
        this.outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
        logicalClock = new LogicalClock();
        this.shutdown = false;
    }

    abstract String getName();
    abstract void run() throws IOException;



    protected Message receive() throws IOException {
        // Request for message destined to me
        writer.println("r:" + this.getName());
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        if (data.equals("null"))
            return null;
        else {
            String[] components = data.split(";");
            return new Message(components);
        }
    }

    protected boolean send(Message message) throws IOException {
        // Send message to server
        writer.println("s:" + message.toString());
        // Read response
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    protected void sendRaw(String s) {
        writer.println(s);
    }

}
