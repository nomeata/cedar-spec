forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && (action has "&\0\0")) && true
};
