forbid(
  principal is a in a::"67",
  action in [Action::"action"],
  resource == a::"67"
) when {
  (true && (({"\0\t": true, "": principal}[""]) in principal)) && false
};
