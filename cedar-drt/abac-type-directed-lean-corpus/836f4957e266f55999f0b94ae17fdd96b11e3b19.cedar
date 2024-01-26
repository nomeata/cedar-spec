forbid(
  principal,
  action == Action::"action",
  resource is a
) when {
  ((true && (if (if (if true then true else true) then (principal in principal) else (principal in principal)) then (principal in principal) else (principal in principal))) && false) && true
};
