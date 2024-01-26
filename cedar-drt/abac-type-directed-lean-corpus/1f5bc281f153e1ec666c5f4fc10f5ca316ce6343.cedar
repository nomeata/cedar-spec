@B("666")
permit(
  principal is a in a::"6",
  action in [Action::"action"],
  resource is a in a::"6"
) when {
  ((true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (if true then (decimal("0.1")) else (decimal("0.1"))) else (decimal("\0"))) == (if ((decimal("0.1")) == (decimal("0.1"))) then (if true then (decimal("0.1")) else (decimal("0.1"))) else (if true then (decimal("0.1")) else (decimal("0.1")))))) && ((decimal("$66")).greaterThan(if (resource has "cissio") then (decimal("")) else (if true then (decimal("0.1")) else (decimal("0.1")))))) && true
};
