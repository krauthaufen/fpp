import http.server, functools
class H(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
        self.send_header('Cross-Origin-Embedder-Policy', 'require-corp')
        super().end_headers()
http.server.HTTPServer(('127.0.0.1', 8732), functools.partial(H, directory='/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/web')).serve_forever()
