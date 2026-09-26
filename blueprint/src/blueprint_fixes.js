// Fixes on top of the plasTeX theme scripts; injected by blueprint/link_decls.py.
$(function() {
  // A link inside a "Uses" pop-up closes the pop-up first, so the target it
  // scrolls to is not hidden behind it.
  $("div.modal-container").on("click", "a", function() {
    $(this).closest("div.modal-container").hide();
  });
  // The theme finds the target of a "#" link with $('#' + id), which breaks on
  // labels such as `def:9.1.a` (':' and '.' are selector syntax).
  $("a.proof").off("click").on("click", function() {
    var ref = $(this).attr("href").split("#")[1];
    var proof = $(document.getElementById(ref));
    proof.show();
    proof.children(".proof_content").each(function() {
      var content = $(this);
      content.show().addClass("hilite");
      setTimeout(function() { content.removeClass("hilite"); }, 1000);
    });
  });
});
