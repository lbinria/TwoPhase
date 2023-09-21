package org.lbee.network;

import org.lbee.instrumentation.clock.SharedClock;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class Server {

    public static void main(String[] args) throws IOException {
        if (args.length < 1) return;

        SharedClock.get("twophase.clock").reset();
        int port = Integer.parseInt(args[0]);


        try (ServerSocket serverSocket = new ServerSocket(port)) {

            System.out.println("Server is listening on port " + port);

            MessageBucket networkMock = new MessageBucket();

            while (true) {
                Socket socket = serverSocket.accept();
                System.out.println("New client connected");

                new ServerThread(socket, networkMock).start();
            }

        } catch (IOException ex) {
            System.out.println("Server exception: " + ex.getMessage());
            ex.printStackTrace();
        }
    }

}
