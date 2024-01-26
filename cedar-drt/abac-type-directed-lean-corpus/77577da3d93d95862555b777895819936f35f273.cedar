permit(
  principal == a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  (true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (if true then (-1) else (-1)) else (if true then (-1) else (-1))) == (if ((decimal("0.1")) == (decimal("0.1"))) then (if false then (-1) else (-1)) else (if true then (-1) else (-1))))) && true
};
