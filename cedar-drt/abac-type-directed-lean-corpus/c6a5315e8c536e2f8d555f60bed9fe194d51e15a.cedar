permit(
  principal == a::"66",
  action in [Action::"action"],
  resource
) when {
  ((true && (if (if (if true then true else true) then (if false then false else false) else (principal in principal)) then (if (if true then false else true) then (if true then true else true) else (if false then false else true)) else (if (if true then true else true) then (if true then true else true) else (if true then true else true)))) && (if (if (if true then true else true) then (if true then true else true) else false) then true else false)) && false
};
