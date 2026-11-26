# web/: a public dashboard for a running node

A static page plus one tiny proxy function, meant for Vercel. The page polls
`/api/summary.json` every two seconds; the function fetches it from your
node's HTTP endpoint and lets Vercel's CDN cache it, so any number of
viewers costs the node one request every couple of seconds.

    your node  --metrics 0.0.0.0:9184   <--   api/proxy.js   <--   index.html in browsers

To host your own:

    # on the node (and allow the port through your firewall)
    leansol --identity identity.key --metrics 0.0.0.0:9184

    # here
    vercel link
    echo -n "http://YOUR.NODE.ADDRESS:9184" | vercel env add LEANSOL_ORIGIN production
    vercel deploy --prod

The node's address lives only in that environment variable, not in the repository.
