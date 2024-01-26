@B("")
@r("")
permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  (true && (principal in action)) && ((if (if true then true else true) then (if true then resource else resource) else (if false then principal else principal)) in principal)
};
