permit(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  (true && principal) && (if (if (if context then false else Action::"action") then (!l::A::"") else A::x::"\0\0") then (if (if principal then principal else principal) then principal else principal) else principal)
};
