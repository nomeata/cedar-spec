permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource
) when {
  (true && (a::"6" in (if ((decimal("0.1")).greaterThanOrEqual(decimal("0.1"))) then (if false then [] else []) else (if false then [] else [])))) && (!(!(principal is a)))
};
