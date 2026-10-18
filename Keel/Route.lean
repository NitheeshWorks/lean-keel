import Keel.APIs.Route

/-!
# Keel.Route: routing

Path templates with typed captures (`str`, `path`, `int`, `float`, `uuid`, or
any lawful `Convertor`), matched with starlette's semantics; `urlFor`;
first-match dispatch; and the HTTP router decision (found, 405, 404). Laws:
`PathTemplate.match_urlFor`, `PathTemplate.urlFor_match`,
`dispatch_found_iff`, `Router.methodNotAllowed_iff`, `Router.notFound_iff`.
-/
