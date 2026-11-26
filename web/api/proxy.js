// The only server-side code of the dashboard: fetch one of three documents
// from the node and hand it on with CDN cache headers, so that many viewers
// cost the node one request every couple of seconds.
//
// LEANSOL_ORIGIN is the node's HTTP endpoint, e.g. http://203.0.113.7:9184
// (set it with `vercel env add LEANSOL_ORIGIN production`).
const TTL = { 'summary.json': 2, 'nodes.json': 15, metrics: 5 };

module.exports = async (req, res) => {
  const origin = process.env.LEANSOL_ORIGIN;
  const doc = String(req.query.p || '');
  if (!origin || !(doc in TTL)) {
    res.status(404).send('not found\n');
    return;
  }
  try {
    const upstream = await fetch(`${origin}/${doc}`, { signal: AbortSignal.timeout(8000) });
    const body = Buffer.from(await upstream.arrayBuffer());
    res.status(upstream.status);
    res.setHeader('Content-Type', upstream.headers.get('content-type') || 'application/octet-stream');
    res.setHeader('Cache-Control', `public, s-maxage=${TTL[doc]}, stale-while-revalidate=30`);
    res.send(body);
  } catch (err) {
    res.status(502).json({ error: 'the node did not answer' });
  }
};
